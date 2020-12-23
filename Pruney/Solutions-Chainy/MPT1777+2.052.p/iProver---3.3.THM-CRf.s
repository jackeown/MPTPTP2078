%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:35 EST 2020

% Result     : Theorem 19.76s
% Output     : CNFRefutation 19.76s
% Verified   : 
% Statistics : Number of formulae       :  241 (2228 expanded)
%              Number of clauses        :  163 ( 498 expanded)
%              Number of leaves         :   27 ( 980 expanded)
%              Depth                    :   29
%              Number of atoms          : 1274 (30678 expanded)
%              Number of equality atoms :  392 (4480 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f45,f44,f43,f42,f41,f40,f39])).

fof(f77,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f75,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_33812,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(X0))
    | r1_tarski(sK0(sK4,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_66556,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_33812])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1778,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_185,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_6])).

cnf(c_186,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1761,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_2328,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1761])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2471,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

cnf(c_2472,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2471])).

cnf(c_3292,plain,
    ( m1_pre_topc(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2328,c_38,c_2472])).

cnf(c_3293,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3292])).

cnf(c_3298,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_3293])).

cnf(c_3956,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3298,c_38,c_2472])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1780,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3379,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1780])).

cnf(c_3387,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3379,c_38,c_2472])).

cnf(c_3388,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3387])).

cnf(c_3393,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_3388])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2469,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_6,c_26])).

cnf(c_2470,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2469])).

cnf(c_3967,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3393,c_38,c_2470])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1777,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2885,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_1777])).

cnf(c_4105,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3967,c_2885])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1005,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2583,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_1005,c_22])).

cnf(c_2584,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2583])).

cnf(c_1007,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2722,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_1007,c_22])).

cnf(c_2723,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2722])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3068,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_5,c_26])).

cnf(c_3069,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3068])).

cnf(c_7231,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4105,c_37,c_38,c_2470,c_2472,c_2584,c_2723,c_3069])).

cnf(c_7232,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7231])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1779,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3287,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1783])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1786,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4335,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_1786])).

cnf(c_4659,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_4335])).

cnf(c_77,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9095,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_77])).

cnf(c_9096,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9095])).

cnf(c_9104,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_9096])).

cnf(c_63113,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9104,c_38,c_2470,c_2723])).

cnf(c_63114,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_63113])).

cnf(c_63169,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_63114])).

cnf(c_64151,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_pre_topc(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3956,c_63169])).

cnf(c_1006,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4530,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_pre_topc(X1,sK4)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_1006,c_22])).

cnf(c_4977,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_pre_topc(sK4,sK4) ),
    inference(resolution,[status(thm)],[c_4530,c_22])).

cnf(c_2128,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5114,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4977,c_33,c_2128,c_2469])).

cnf(c_5128,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_5114,c_7])).

cnf(c_5129,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5128])).

cnf(c_1769,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7242,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_1777])).

cnf(c_7969,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7242,c_37,c_38,c_2470,c_2584,c_2723,c_3069])).

cnf(c_7976,plain,
    ( m1_pre_topc(sK1,sK4) != iProver_top
    | m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_7969])).

cnf(c_3448,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3451,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3448])).

cnf(c_3438,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_4899,plain,
    ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3438])).

cnf(c_4900,plain,
    ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4899])).

cnf(c_8494,plain,
    ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7976,c_38,c_2472,c_3451,c_4900])).

cnf(c_9123,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8494,c_9096])).

cnf(c_64176,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64151,c_38,c_2470,c_2472,c_2723,c_5129,c_9123])).

cnf(c_64178,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_22,c_64176])).

cnf(c_19,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1775,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_499,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_500,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_504,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_25])).

cnf(c_505,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_504])).

cnf(c_552,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_505,c_14])).

cnf(c_597,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X7,u1_struct_0(X0))
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
    | X4 != X5
    | sK0(X6,X5) != X7
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_552])).

cnf(c_598,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
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
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_623,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
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
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_598,c_577])).

cnf(c_644,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_5,c_6])).

cnf(c_1759,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(sK0(X1,X4),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1904,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1759])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3806,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1904,c_39,c_40,c_41])).

cnf(c_3807,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3806])).

cnf(c_3810,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3807])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5380,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3810,c_44,c_48])).

cnf(c_5381,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5380])).

cnf(c_5386,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_5381])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1000,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1881,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1978,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_2242,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_644,c_18])).

cnf(c_2243,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_2242])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2333,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK3,sK4)
    | r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2243,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_27,c_26,c_23,c_20])).

cnf(c_2334,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_2333])).

cnf(c_2335,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2334])).

cnf(c_1001,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2010,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_2313,plain,
    ( X0 != sK7
    | X0 = sK6
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_2591,plain,
    ( sK7 != sK7
    | sK7 = sK6
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1954,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X1 != u1_struct_0(sK4)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_3095,plain,
    ( m1_subset_1(sK7,X0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X0 != u1_struct_0(sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_4044,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_3095])).

cnf(c_4045,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK7 != sK6
    | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4044])).

cnf(c_10355,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5386,c_38,c_49,c_19,c_1881,c_1978,c_2335,c_2472,c_2591,c_3298,c_4045])).

cnf(c_10359,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_10355])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_52,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1949,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | m1_subset_1(sK6,X0)
    | X0 != u1_struct_0(sK3)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_2109,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | m1_subset_1(sK6,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_2111,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK7
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_2110,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_2794,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1775])).

cnf(c_5387,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_5381])).

cnf(c_10362,plain,
    ( r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10359,c_36,c_37,c_38,c_42,c_45,c_49,c_50,c_19,c_52,c_2111,c_2110,c_2472,c_3298,c_5387])).

cnf(c_65614,plain,
    ( r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_64178,c_10362])).

cnf(c_65833,plain,
    ( ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_65614])).

cnf(c_1928,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66556,c_65833,c_3068,c_2469,c_1928,c_21,c_27,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.76/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.76/3.00  
% 19.76/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.76/3.00  
% 19.76/3.00  ------  iProver source info
% 19.76/3.00  
% 19.76/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.76/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.76/3.00  git: non_committed_changes: false
% 19.76/3.00  git: last_make_outside_of_git: false
% 19.76/3.00  
% 19.76/3.00  ------ 
% 19.76/3.00  ------ Parsing...
% 19.76/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.76/3.00  
% 19.76/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 19.76/3.00  
% 19.76/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.76/3.00  
% 19.76/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.76/3.00  ------ Proving...
% 19.76/3.00  ------ Problem Properties 
% 19.76/3.00  
% 19.76/3.00  
% 19.76/3.00  clauses                                 31
% 19.76/3.00  conjectures                             17
% 19.76/3.00  EPR                                     18
% 19.76/3.00  Horn                                    28
% 19.76/3.00  unary                                   18
% 19.76/3.00  binary                                  3
% 19.76/3.00  lits                                    89
% 19.76/3.00  lits eq                                 7
% 19.76/3.00  fd_pure                                 0
% 19.76/3.00  fd_pseudo                               0
% 19.76/3.00  fd_cond                                 0
% 19.76/3.00  fd_pseudo_cond                          1
% 19.76/3.00  AC symbols                              0
% 19.76/3.00  
% 19.76/3.00  ------ Input Options Time Limit: Unbounded
% 19.76/3.00  
% 19.76/3.00  
% 19.76/3.00  ------ 
% 19.76/3.00  Current options:
% 19.76/3.00  ------ 
% 19.76/3.00  
% 19.76/3.00  
% 19.76/3.00  
% 19.76/3.00  
% 19.76/3.00  ------ Proving...
% 19.76/3.00  
% 19.76/3.00  
% 19.76/3.00  % SZS status Theorem for theBenchmark.p
% 19.76/3.00  
% 19.76/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.76/3.00  
% 19.76/3.00  fof(f2,axiom,(
% 19.76/3.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f34,plain,(
% 19.76/3.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.76/3.00    inference(nnf_transformation,[],[f2])).
% 19.76/3.00  
% 19.76/3.00  fof(f50,plain,(
% 19.76/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.76/3.00    inference(cnf_transformation,[],[f34])).
% 19.76/3.00  
% 19.76/3.00  fof(f13,conjecture,(
% 19.76/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f14,negated_conjecture,(
% 19.76/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 19.76/3.00    inference(negated_conjecture,[],[f13])).
% 19.76/3.00  
% 19.76/3.00  fof(f30,plain,(
% 19.76/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.76/3.00    inference(ennf_transformation,[],[f14])).
% 19.76/3.00  
% 19.76/3.00  fof(f31,plain,(
% 19.76/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.76/3.00    inference(flattening,[],[f30])).
% 19.76/3.00  
% 19.76/3.00  fof(f45,plain,(
% 19.76/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f44,plain,(
% 19.76/3.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f43,plain,(
% 19.76/3.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK5,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f42,plain,(
% 19.76/3.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f41,plain,(
% 19.76/3.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f40,plain,(
% 19.76/3.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f39,plain,(
% 19.76/3.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f46,plain,(
% 19.76/3.00    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 19.76/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f45,f44,f43,f42,f41,f40,f39])).
% 19.76/3.00  
% 19.76/3.00  fof(f77,plain,(
% 19.76/3.00    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f10,axiom,(
% 19.76/3.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f25,plain,(
% 19.76/3.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 19.76/3.00    inference(ennf_transformation,[],[f10])).
% 19.76/3.00  
% 19.76/3.00  fof(f60,plain,(
% 19.76/3.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f25])).
% 19.76/3.00  
% 19.76/3.00  fof(f6,axiom,(
% 19.76/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f19,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.76/3.00    inference(ennf_transformation,[],[f6])).
% 19.76/3.00  
% 19.76/3.00  fof(f35,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.76/3.00    inference(nnf_transformation,[],[f19])).
% 19.76/3.00  
% 19.76/3.00  fof(f55,plain,(
% 19.76/3.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f35])).
% 19.76/3.00  
% 19.76/3.00  fof(f4,axiom,(
% 19.76/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f17,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.76/3.00    inference(ennf_transformation,[],[f4])).
% 19.76/3.00  
% 19.76/3.00  fof(f53,plain,(
% 19.76/3.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f17])).
% 19.76/3.00  
% 19.76/3.00  fof(f66,plain,(
% 19.76/3.00    l1_pre_topc(sK1)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f71,plain,(
% 19.76/3.00    m1_pre_topc(sK3,sK1)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f5,axiom,(
% 19.76/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f18,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 19.76/3.00    inference(ennf_transformation,[],[f5])).
% 19.76/3.00  
% 19.76/3.00  fof(f54,plain,(
% 19.76/3.00    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f18])).
% 19.76/3.00  
% 19.76/3.00  fof(f73,plain,(
% 19.76/3.00    m1_pre_topc(sK4,sK1)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f11,axiom,(
% 19.76/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f26,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.76/3.00    inference(ennf_transformation,[],[f11])).
% 19.76/3.00  
% 19.76/3.00  fof(f27,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.76/3.00    inference(flattening,[],[f26])).
% 19.76/3.00  
% 19.76/3.00  fof(f61,plain,(
% 19.76/3.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f27])).
% 19.76/3.00  
% 19.76/3.00  fof(f65,plain,(
% 19.76/3.00    v2_pre_topc(sK1)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f3,axiom,(
% 19.76/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f15,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.76/3.00    inference(ennf_transformation,[],[f3])).
% 19.76/3.00  
% 19.76/3.00  fof(f16,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.76/3.00    inference(flattening,[],[f15])).
% 19.76/3.00  
% 19.76/3.00  fof(f52,plain,(
% 19.76/3.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f16])).
% 19.76/3.00  
% 19.76/3.00  fof(f9,axiom,(
% 19.76/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f24,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.76/3.00    inference(ennf_transformation,[],[f9])).
% 19.76/3.00  
% 19.76/3.00  fof(f59,plain,(
% 19.76/3.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f24])).
% 19.76/3.00  
% 19.76/3.00  fof(f1,axiom,(
% 19.76/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f32,plain,(
% 19.76/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.76/3.00    inference(nnf_transformation,[],[f1])).
% 19.76/3.00  
% 19.76/3.00  fof(f33,plain,(
% 19.76/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.76/3.00    inference(flattening,[],[f32])).
% 19.76/3.00  
% 19.76/3.00  fof(f49,plain,(
% 19.76/3.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f33])).
% 19.76/3.00  
% 19.76/3.00  fof(f80,plain,(
% 19.76/3.00    sK6 = sK7),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f81,plain,(
% 19.76/3.00    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f8,axiom,(
% 19.76/3.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f22,plain,(
% 19.76/3.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.76/3.00    inference(ennf_transformation,[],[f8])).
% 19.76/3.00  
% 19.76/3.00  fof(f23,plain,(
% 19.76/3.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.76/3.00    inference(flattening,[],[f22])).
% 19.76/3.00  
% 19.76/3.00  fof(f36,plain,(
% 19.76/3.00    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 19.76/3.00    introduced(choice_axiom,[])).
% 19.76/3.00  
% 19.76/3.00  fof(f37,plain,(
% 19.76/3.00    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.76/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).
% 19.76/3.00  
% 19.76/3.00  fof(f58,plain,(
% 19.76/3.00    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f37])).
% 19.76/3.00  
% 19.76/3.00  fof(f12,axiom,(
% 19.76/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f28,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.76/3.00    inference(ennf_transformation,[],[f12])).
% 19.76/3.00  
% 19.76/3.00  fof(f29,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.76/3.00    inference(flattening,[],[f28])).
% 19.76/3.00  
% 19.76/3.00  fof(f38,plain,(
% 19.76/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.76/3.00    inference(nnf_transformation,[],[f29])).
% 19.76/3.00  
% 19.76/3.00  fof(f63,plain,(
% 19.76/3.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f38])).
% 19.76/3.00  
% 19.76/3.00  fof(f85,plain,(
% 19.76/3.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.76/3.00    inference(equality_resolution,[],[f63])).
% 19.76/3.00  
% 19.76/3.00  fof(f75,plain,(
% 19.76/3.00    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f74,plain,(
% 19.76/3.00    v1_funct_1(sK5)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f7,axiom,(
% 19.76/3.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.76/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.76/3.00  
% 19.76/3.00  fof(f20,plain,(
% 19.76/3.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.76/3.00    inference(ennf_transformation,[],[f7])).
% 19.76/3.00  
% 19.76/3.00  fof(f21,plain,(
% 19.76/3.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.76/3.00    inference(flattening,[],[f20])).
% 19.76/3.00  
% 19.76/3.00  fof(f57,plain,(
% 19.76/3.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.76/3.00    inference(cnf_transformation,[],[f21])).
% 19.76/3.00  
% 19.76/3.00  fof(f67,plain,(
% 19.76/3.00    ~v2_struct_0(sK2)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f68,plain,(
% 19.76/3.00    v2_pre_topc(sK2)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f69,plain,(
% 19.76/3.00    l1_pre_topc(sK2)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f72,plain,(
% 19.76/3.00    ~v2_struct_0(sK4)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f76,plain,(
% 19.76/3.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f78,plain,(
% 19.76/3.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f64,plain,(
% 19.76/3.00    ~v2_struct_0(sK1)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f70,plain,(
% 19.76/3.00    ~v2_struct_0(sK3)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f79,plain,(
% 19.76/3.00    m1_subset_1(sK7,u1_struct_0(sK3))),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  fof(f82,plain,(
% 19.76/3.00    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 19.76/3.00    inference(cnf_transformation,[],[f46])).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4,plain,
% 19.76/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_33812,plain,
% 19.76/3.00      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(X0))
% 19.76/3.00      | r1_tarski(sK0(sK4,sK6),X0) ),
% 19.76/3.00      inference(instantiation,[status(thm)],[c_4]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_66556,plain,
% 19.76/3.00      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 19.76/3.00      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
% 19.76/3.00      inference(instantiation,[status(thm)],[c_33812]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_22,negated_conjecture,
% 19.76/3.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
% 19.76/3.00      inference(cnf_transformation,[],[f77]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_13,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 19.76/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1778,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X0) = iProver_top
% 19.76/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_9,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.76/3.00      | ~ l1_pre_topc(X0)
% 19.76/3.00      | ~ l1_pre_topc(X1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_6,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.76/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_185,plain,
% 19.76/3.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.76/3.00      | ~ m1_pre_topc(X0,X1)
% 19.76/3.00      | ~ l1_pre_topc(X1) ),
% 19.76/3.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_6]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_186,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.76/3.00      | ~ l1_pre_topc(X1) ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_185]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1761,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2328,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) = iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_22,c_1761]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_33,negated_conjecture,
% 19.76/3.00      ( l1_pre_topc(sK1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f66]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_38,plain,
% 19.76/3.00      ( l1_pre_topc(sK1) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_28,negated_conjecture,
% 19.76/3.00      ( m1_pre_topc(sK3,sK1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f71]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2471,plain,
% 19.76/3.00      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_6,c_28]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2472,plain,
% 19.76/3.00      ( l1_pre_topc(sK1) != iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_2471]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3292,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK4) = iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK3) != iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_2328,c_38,c_2472]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3293,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) = iProver_top ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_3292]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3298,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,sK4) = iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_1778,c_3293]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3956,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_3298,c_38,c_2472]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_7,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1)
% 19.76/3.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.76/3.00      | ~ l1_pre_topc(X1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1780,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) = iProver_top
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3379,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_22,c_1780]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3387,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK3) = iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_3379,c_38,c_2472]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3388,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_3387]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3393,plain,
% 19.76/3.00      ( m1_pre_topc(sK4,sK3) = iProver_top
% 19.76/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_1778,c_3388]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_26,negated_conjecture,
% 19.76/3.00      ( m1_pre_topc(sK4,sK1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2469,plain,
% 19.76/3.00      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK4) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_6,c_26]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2470,plain,
% 19.76/3.00      ( l1_pre_topc(sK1) != iProver_top
% 19.76/3.00      | l1_pre_topc(sK4) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_2469]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3967,plain,
% 19.76/3.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_3393,c_38,c_2470]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_14,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.76/3.00      | ~ m1_pre_topc(X2,X0)
% 19.76/3.00      | m1_pre_topc(X2,X1)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1777,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X2,X0) != iProver_top
% 19.76/3.00      | m1_pre_topc(X2,X1) = iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top
% 19.76/3.00      | v2_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2885,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X2,X0) != iProver_top
% 19.76/3.00      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top
% 19.76/3.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 19.76/3.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_1761,c_1777]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4105,plain,
% 19.76/3.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.76/3.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_3967,c_2885]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_34,negated_conjecture,
% 19.76/3.00      ( v2_pre_topc(sK1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_37,plain,
% 19.76/3.00      ( v2_pre_topc(sK1) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1005,plain,
% 19.76/3.00      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 19.76/3.00      theory(equality) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2583,plain,
% 19.76/3.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 19.76/3.00      | ~ v2_pre_topc(sK4) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_1005,c_22]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2584,plain,
% 19.76/3.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | v2_pre_topc(sK4) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_2583]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1007,plain,
% 19.76/3.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 19.76/3.00      theory(equality) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2722,plain,
% 19.76/3.00      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 19.76/3.00      | ~ l1_pre_topc(sK4) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_1007,c_22]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2723,plain,
% 19.76/3.00      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_2722]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_5,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | v2_pre_topc(X0) ),
% 19.76/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3068,plain,
% 19.76/3.00      ( ~ l1_pre_topc(sK1) | ~ v2_pre_topc(sK1) | v2_pre_topc(sK4) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_5,c_26]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3069,plain,
% 19.76/3.00      ( l1_pre_topc(sK1) != iProver_top
% 19.76/3.00      | v2_pre_topc(sK1) != iProver_top
% 19.76/3.00      | v2_pre_topc(sK4) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_3068]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_7231,plain,
% 19.76/3.00      ( m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_4105,c_37,c_38,c_2470,c_2472,c_2584,c_2723,c_3069]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_7232,plain,
% 19.76/3.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_7231]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_12,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.76/3.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.76/3.00      | ~ l1_pre_topc(X1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1779,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1783,plain,
% 19.76/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.76/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3287,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_1779,c_1783]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_0,plain,
% 19.76/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.76/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1786,plain,
% 19.76/3.00      ( X0 = X1
% 19.76/3.00      | r1_tarski(X0,X1) != iProver_top
% 19.76/3.00      | r1_tarski(X1,X0) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4335,plain,
% 19.76/3.00      ( u1_struct_0(X0) = u1_struct_0(X1)
% 19.76/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 19.76/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_3287,c_1786]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4659,plain,
% 19.76/3.00      ( u1_struct_0(X0) = u1_struct_0(X1)
% 19.76/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | l1_pre_topc(X0) != iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_3287,c_4335]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_77,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top
% 19.76/3.00      | l1_pre_topc(X0) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_9095,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.00      | u1_struct_0(X0) = u1_struct_0(X1)
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_4659,c_77]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_9096,plain,
% 19.76/3.00      ( u1_struct_0(X0) = u1_struct_0(X1)
% 19.76/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_9095]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_9104,plain,
% 19.76/3.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0)
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
% 19.76/3.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_7232,c_9096]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_63113,plain,
% 19.76/3.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0) ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_9104,c_38,c_2470,c_2723]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_63114,plain,
% 19.76/3.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0)
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_63113]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_63169,plain,
% 19.76/3.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(X0)
% 19.76/3.00      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.00      | m1_pre_topc(sK4,X0) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_22,c_63114]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_64151,plain,
% 19.76/3.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 19.76/3.00      | m1_pre_topc(sK4,sK3) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_3956,c_63169]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1006,plain,
% 19.76/3.00      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.76/3.00      theory(equality) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4530,plain,
% 19.76/3.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 19.76/3.00      | ~ m1_pre_topc(X1,sK4)
% 19.76/3.00      | X0 != X1 ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_1006,c_22]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4977,plain,
% 19.76/3.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 19.76/3.00      | ~ m1_pre_topc(sK4,sK4) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_4530,c_22]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_2128,plain,
% 19.76/3.00      ( m1_pre_topc(sK4,sK4) | ~ l1_pre_topc(sK4) ),
% 19.76/3.00      inference(instantiation,[status(thm)],[c_13]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_5114,plain,
% 19.76/3.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_4977,c_33,c_2128,c_2469]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_5128,plain,
% 19.76/3.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3)
% 19.76/3.00      | ~ l1_pre_topc(sK3) ),
% 19.76/3.00      inference(resolution,[status(thm)],[c_5114,c_7]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_5129,plain,
% 19.76/3.00      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3) = iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_5128]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1769,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_7242,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | m1_pre_topc(X1,sK4) != iProver_top
% 19.76/3.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 19.76/3.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_7232,c_1777]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_7969,plain,
% 19.76/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.76/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | m1_pre_topc(X1,sK4) != iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_7242,c_37,c_38,c_2470,c_2584,c_2723,c_3069]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_7976,plain,
% 19.76/3.00      ( m1_pre_topc(sK1,sK4) != iProver_top
% 19.76/3.00      | m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_1769,c_7969]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3448,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 19.76/3.00      inference(instantiation,[status(thm)],[c_13]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3451,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,sK3) = iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_3448]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_3438,plain,
% 19.76/3.00      ( ~ m1_pre_topc(sK3,X0)
% 19.76/3.00      | m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 19.76/3.00      | ~ l1_pre_topc(X0) ),
% 19.76/3.00      inference(instantiation,[status(thm)],[c_186]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4899,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 19.76/3.00      | ~ m1_pre_topc(sK3,sK3)
% 19.76/3.00      | ~ l1_pre_topc(sK3) ),
% 19.76/3.00      inference(instantiation,[status(thm)],[c_3438]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_4900,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.76/3.00      | m1_pre_topc(sK3,sK3) != iProver_top
% 19.76/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_4899]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_8494,plain,
% 19.76/3.00      ( m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_7976,c_38,c_2472,c_3451,c_4900]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_9123,plain,
% 19.76/3.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 19.76/3.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK3) != iProver_top
% 19.76/3.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_8494,c_9096]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_64176,plain,
% 19.76/3.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_64151,c_38,c_2470,c_2472,c_2723,c_5129,c_9123]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_64178,plain,
% 19.76/3.00      ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
% 19.76/3.00      inference(superposition,[status(thm)],[c_22,c_64176]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_19,negated_conjecture,
% 19.76/3.00      ( sK6 = sK7 ),
% 19.76/3.00      inference(cnf_transformation,[],[f80]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_18,negated_conjecture,
% 19.76/3.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 19.76/3.00      inference(cnf_transformation,[],[f81]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_1775,plain,
% 19.76/3.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 19.76/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_11,plain,
% 19.76/3.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 19.76/3.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | ~ l1_pre_topc(X0)
% 19.76/3.00      | ~ v2_pre_topc(X0) ),
% 19.76/3.00      inference(cnf_transformation,[],[f58]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_15,plain,
% 19.76/3.00      ( r1_tmap_1(X0,X1,X2,X3)
% 19.76/3.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 19.76/3.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 19.76/3.00      | ~ m1_connsp_2(X6,X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X4,X5)
% 19.76/3.00      | ~ m1_pre_topc(X4,X0)
% 19.76/3.00      | ~ m1_pre_topc(X0,X5)
% 19.76/3.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 19.76/3.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.76/3.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 19.76/3.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 19.76/3.00      | ~ v1_funct_1(X2)
% 19.76/3.00      | v2_struct_0(X5)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X4)
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | ~ l1_pre_topc(X5)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X5)
% 19.76/3.00      | ~ v2_pre_topc(X1) ),
% 19.76/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_24,negated_conjecture,
% 19.76/3.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 19.76/3.00      inference(cnf_transformation,[],[f75]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_499,plain,
% 19.76/3.00      ( r1_tmap_1(X0,X1,X2,X3)
% 19.76/3.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 19.76/3.00      | ~ m1_connsp_2(X6,X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X4,X5)
% 19.76/3.00      | ~ m1_pre_topc(X4,X0)
% 19.76/3.00      | ~ m1_pre_topc(X0,X5)
% 19.76/3.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 19.76/3.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.76/3.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 19.76/3.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 19.76/3.00      | ~ v1_funct_1(X2)
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X5)
% 19.76/3.00      | v2_struct_0(X4)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X5)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X5)
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 19.76/3.00      | sK5 != X2 ),
% 19.76/3.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_500,plain,
% 19.76/3.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.00      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.00      | ~ m1_connsp_2(X5,X3,X4)
% 19.76/3.00      | ~ m1_pre_topc(X0,X2)
% 19.76/3.00      | ~ m1_pre_topc(X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X3,X2)
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 19.76/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 19.76/3.00      | ~ v1_funct_1(sK5)
% 19.76/3.00      | v2_struct_0(X3)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X2)
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X2)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X2)
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.00      inference(unflattening,[status(thm)],[c_499]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_25,negated_conjecture,
% 19.76/3.00      ( v1_funct_1(sK5) ),
% 19.76/3.00      inference(cnf_transformation,[],[f74]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_504,plain,
% 19.76/3.00      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_pre_topc(X3,X2)
% 19.76/3.00      | ~ m1_pre_topc(X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X0,X2)
% 19.76/3.00      | ~ m1_connsp_2(X5,X3,X4)
% 19.76/3.00      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.00      | v2_struct_0(X3)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X2)
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X2)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X2)
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.00      inference(global_propositional_subsumption,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_500,c_25]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_505,plain,
% 19.76/3.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.00      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.00      | ~ m1_connsp_2(X5,X3,X4)
% 19.76/3.00      | ~ m1_pre_topc(X0,X2)
% 19.76/3.00      | ~ m1_pre_topc(X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X3,X2)
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 19.76/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X2)
% 19.76/3.00      | v2_struct_0(X3)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X2)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X2)
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.00      inference(renaming,[status(thm)],[c_504]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_552,plain,
% 19.76/3.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.00      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.00      | ~ m1_connsp_2(X5,X3,X4)
% 19.76/3.00      | ~ m1_pre_topc(X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X3,X2)
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 19.76/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X2)
% 19.76/3.00      | v2_struct_0(X3)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X2)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X2)
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.00      inference(forward_subsumption_resolution,
% 19.76/3.00                [status(thm)],
% 19.76/3.00                [c_505,c_14]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_597,plain,
% 19.76/3.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.00      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.00      | ~ m1_pre_topc(X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X3,X2)
% 19.76/3.00      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
% 19.76/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.00      | ~ r1_tarski(X7,u1_struct_0(X0))
% 19.76/3.00      | v2_struct_0(X6)
% 19.76/3.00      | v2_struct_0(X3)
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X2)
% 19.76/3.00      | ~ l1_pre_topc(X6)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X2)
% 19.76/3.00      | ~ v2_pre_topc(X6)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X2)
% 19.76/3.00      | X3 != X6
% 19.76/3.00      | X4 != X5
% 19.76/3.00      | sK0(X6,X5) != X7
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.00      inference(resolution_lifted,[status(thm)],[c_11,c_552]) ).
% 19.76/3.00  
% 19.76/3.00  cnf(c_598,plain,
% 19.76/3.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.00      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.00      | ~ m1_pre_topc(X0,X3)
% 19.76/3.00      | ~ m1_pre_topc(X3,X2)
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.00      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
% 19.76/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.00      | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
% 19.76/3.00      | v2_struct_0(X0)
% 19.76/3.00      | v2_struct_0(X1)
% 19.76/3.00      | v2_struct_0(X2)
% 19.76/3.00      | v2_struct_0(X3)
% 19.76/3.00      | ~ l1_pre_topc(X1)
% 19.76/3.00      | ~ l1_pre_topc(X2)
% 19.76/3.00      | ~ l1_pre_topc(X3)
% 19.76/3.00      | ~ v2_pre_topc(X1)
% 19.76/3.00      | ~ v2_pre_topc(X2)
% 19.76/3.00      | ~ v2_pre_topc(X3)
% 19.76/3.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.00      inference(unflattening,[status(thm)],[c_597]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_10,plain,
% 19.76/3.01      ( ~ m1_connsp_2(X0,X1,X2)
% 19.76/3.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.76/3.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.76/3.01      | v2_struct_0(X1)
% 19.76/3.01      | ~ l1_pre_topc(X1)
% 19.76/3.01      | ~ v2_pre_topc(X1) ),
% 19.76/3.01      inference(cnf_transformation,[],[f57]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_576,plain,
% 19.76/3.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.76/3.01      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 19.76/3.01      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 19.76/3.01      | v2_struct_0(X1)
% 19.76/3.01      | v2_struct_0(X3)
% 19.76/3.01      | ~ l1_pre_topc(X1)
% 19.76/3.01      | ~ l1_pre_topc(X3)
% 19.76/3.01      | ~ v2_pre_topc(X1)
% 19.76/3.01      | ~ v2_pre_topc(X3)
% 19.76/3.01      | X3 != X1
% 19.76/3.01      | X2 != X0
% 19.76/3.01      | sK0(X3,X2) != X4 ),
% 19.76/3.01      inference(resolution_lifted,[status(thm)],[c_10,c_11]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_577,plain,
% 19.76/3.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.76/3.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.76/3.01      | v2_struct_0(X1)
% 19.76/3.01      | ~ l1_pre_topc(X1)
% 19.76/3.01      | ~ v2_pre_topc(X1) ),
% 19.76/3.01      inference(unflattening,[status(thm)],[c_576]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_623,plain,
% 19.76/3.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.01      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.01      | ~ m1_pre_topc(X0,X3)
% 19.76/3.01      | ~ m1_pre_topc(X3,X2)
% 19.76/3.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.01      | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
% 19.76/3.01      | v2_struct_0(X0)
% 19.76/3.01      | v2_struct_0(X1)
% 19.76/3.01      | v2_struct_0(X2)
% 19.76/3.01      | v2_struct_0(X3)
% 19.76/3.01      | ~ l1_pre_topc(X1)
% 19.76/3.01      | ~ l1_pre_topc(X2)
% 19.76/3.01      | ~ l1_pre_topc(X3)
% 19.76/3.01      | ~ v2_pre_topc(X1)
% 19.76/3.01      | ~ v2_pre_topc(X2)
% 19.76/3.01      | ~ v2_pre_topc(X3)
% 19.76/3.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.01      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.01      inference(forward_subsumption_resolution,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_598,c_577]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_644,plain,
% 19.76/3.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 19.76/3.01      | r1_tmap_1(X3,X1,sK5,X4)
% 19.76/3.01      | ~ m1_pre_topc(X0,X3)
% 19.76/3.01      | ~ m1_pre_topc(X3,X2)
% 19.76/3.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 19.76/3.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 19.76/3.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.76/3.01      | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
% 19.76/3.01      | v2_struct_0(X0)
% 19.76/3.01      | v2_struct_0(X1)
% 19.76/3.01      | v2_struct_0(X2)
% 19.76/3.01      | v2_struct_0(X3)
% 19.76/3.01      | ~ l1_pre_topc(X1)
% 19.76/3.01      | ~ l1_pre_topc(X2)
% 19.76/3.01      | ~ v2_pre_topc(X1)
% 19.76/3.01      | ~ v2_pre_topc(X2)
% 19.76/3.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 19.76/3.01      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 19.76/3.01      inference(forward_subsumption_resolution,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_623,c_5,c_6]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1759,plain,
% 19.76/3.01      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 19.76/3.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 19.76/3.01      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
% 19.76/3.01      | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
% 19.76/3.01      | m1_pre_topc(X2,X1) != iProver_top
% 19.76/3.01      | m1_pre_topc(X1,X3) != iProver_top
% 19.76/3.01      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 19.76/3.01      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(X1,X4),u1_struct_0(X2)) != iProver_top
% 19.76/3.01      | v2_struct_0(X0) = iProver_top
% 19.76/3.01      | v2_struct_0(X2) = iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | v2_struct_0(X3) = iProver_top
% 19.76/3.01      | l1_pre_topc(X0) != iProver_top
% 19.76/3.01      | l1_pre_topc(X3) != iProver_top
% 19.76/3.01      | v2_pre_topc(X0) != iProver_top
% 19.76/3.01      | v2_pre_topc(X3) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1904,plain,
% 19.76/3.01      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 19.76/3.01      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 19.76/3.01      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 19.76/3.01      | m1_pre_topc(X0,X2) != iProver_top
% 19.76/3.01      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.01      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | v2_struct_0(X0) = iProver_top
% 19.76/3.01      | v2_struct_0(X2) = iProver_top
% 19.76/3.01      | v2_struct_0(sK2) = iProver_top
% 19.76/3.01      | l1_pre_topc(X2) != iProver_top
% 19.76/3.01      | l1_pre_topc(sK2) != iProver_top
% 19.76/3.01      | v2_pre_topc(X2) != iProver_top
% 19.76/3.01      | v2_pre_topc(sK2) != iProver_top ),
% 19.76/3.01      inference(equality_resolution,[status(thm)],[c_1759]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_32,negated_conjecture,
% 19.76/3.01      ( ~ v2_struct_0(sK2) ),
% 19.76/3.01      inference(cnf_transformation,[],[f67]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_39,plain,
% 19.76/3.01      ( v2_struct_0(sK2) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_31,negated_conjecture,
% 19.76/3.01      ( v2_pre_topc(sK2) ),
% 19.76/3.01      inference(cnf_transformation,[],[f68]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_40,plain,
% 19.76/3.01      ( v2_pre_topc(sK2) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_30,negated_conjecture,
% 19.76/3.01      ( l1_pre_topc(sK2) ),
% 19.76/3.01      inference(cnf_transformation,[],[f69]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_41,plain,
% 19.76/3.01      ( l1_pre_topc(sK2) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_3806,plain,
% 19.76/3.01      ( v2_pre_topc(X2) != iProver_top
% 19.76/3.01      | v2_struct_0(X2) = iProver_top
% 19.76/3.01      | v2_struct_0(X0) = iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 19.76/3.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.01      | m1_pre_topc(X0,X2) != iProver_top
% 19.76/3.01      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 19.76/3.01      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 19.76/3.01      | u1_struct_0(X0) != u1_struct_0(sK4)
% 19.76/3.01      | l1_pre_topc(X2) != iProver_top ),
% 19.76/3.01      inference(global_propositional_subsumption,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_1904,c_39,c_40,c_41]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_3807,plain,
% 19.76/3.01      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 19.76/3.01      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 19.76/3.01      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 19.76/3.01      | m1_pre_topc(X0,X2) != iProver_top
% 19.76/3.01      | m1_pre_topc(X1,X0) != iProver_top
% 19.76/3.01      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | v2_struct_0(X0) = iProver_top
% 19.76/3.01      | v2_struct_0(X2) = iProver_top
% 19.76/3.01      | l1_pre_topc(X2) != iProver_top
% 19.76/3.01      | v2_pre_topc(X2) != iProver_top ),
% 19.76/3.01      inference(renaming,[status(thm)],[c_3806]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_3810,plain,
% 19.76/3.01      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 19.76/3.01      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 19.76/3.01      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.01      | m1_pre_topc(sK4,X1) != iProver_top
% 19.76/3.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | v2_struct_0(X0) = iProver_top
% 19.76/3.01      | v2_struct_0(sK4) = iProver_top
% 19.76/3.01      | l1_pre_topc(X1) != iProver_top
% 19.76/3.01      | v2_pre_topc(X1) != iProver_top ),
% 19.76/3.01      inference(equality_resolution,[status(thm)],[c_3807]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_27,negated_conjecture,
% 19.76/3.01      ( ~ v2_struct_0(sK4) ),
% 19.76/3.01      inference(cnf_transformation,[],[f72]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_44,plain,
% 19.76/3.01      ( v2_struct_0(sK4) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_23,negated_conjecture,
% 19.76/3.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 19.76/3.01      inference(cnf_transformation,[],[f76]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_48,plain,
% 19.76/3.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_5380,plain,
% 19.76/3.01      ( v2_struct_0(X0) = iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 19.76/3.01      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 19.76/3.01      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.01      | m1_pre_topc(sK4,X1) != iProver_top
% 19.76/3.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 19.76/3.01      | l1_pre_topc(X1) != iProver_top
% 19.76/3.01      | v2_pre_topc(X1) != iProver_top ),
% 19.76/3.01      inference(global_propositional_subsumption,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_3810,c_44,c_48]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_5381,plain,
% 19.76/3.01      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 19.76/3.01      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 19.76/3.01      | m1_pre_topc(X0,sK4) != iProver_top
% 19.76/3.01      | m1_pre_topc(sK4,X1) != iProver_top
% 19.76/3.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
% 19.76/3.01      | v2_struct_0(X1) = iProver_top
% 19.76/3.01      | v2_struct_0(X0) = iProver_top
% 19.76/3.01      | l1_pre_topc(X1) != iProver_top
% 19.76/3.01      | v2_pre_topc(X1) != iProver_top ),
% 19.76/3.01      inference(renaming,[status(thm)],[c_5380]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_5386,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 19.76/3.01      | m1_pre_topc(sK3,sK4) != iProver_top
% 19.76/3.01      | m1_pre_topc(sK4,sK1) != iProver_top
% 19.76/3.01      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) != iProver_top
% 19.76/3.01      | v2_struct_0(sK1) = iProver_top
% 19.76/3.01      | v2_struct_0(sK3) = iProver_top
% 19.76/3.01      | l1_pre_topc(sK1) != iProver_top
% 19.76/3.01      | v2_pre_topc(sK1) != iProver_top ),
% 19.76/3.01      inference(superposition,[status(thm)],[c_1775,c_5381]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_21,negated_conjecture,
% 19.76/3.01      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 19.76/3.01      inference(cnf_transformation,[],[f78]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_49,plain,
% 19.76/3.01      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1000,plain,( X0 = X0 ),theory(equality) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1881,plain,
% 19.76/3.01      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1978,plain,
% 19.76/3.01      ( sK7 = sK7 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2242,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 19.76/3.01      | ~ m1_pre_topc(sK3,sK4)
% 19.76/3.01      | ~ m1_pre_topc(sK4,sK1)
% 19.76/3.01      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 19.76/3.01      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 19.76/3.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 19.76/3.01      | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3))
% 19.76/3.01      | v2_struct_0(sK1)
% 19.76/3.01      | v2_struct_0(sK3)
% 19.76/3.01      | v2_struct_0(sK2)
% 19.76/3.01      | v2_struct_0(sK4)
% 19.76/3.01      | ~ l1_pre_topc(sK1)
% 19.76/3.01      | ~ l1_pre_topc(sK2)
% 19.76/3.01      | ~ v2_pre_topc(sK1)
% 19.76/3.01      | ~ v2_pre_topc(sK2)
% 19.76/3.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 19.76/3.01      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 19.76/3.01      inference(resolution,[status(thm)],[c_644,c_18]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2243,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 19.76/3.01      | ~ m1_pre_topc(sK3,sK4)
% 19.76/3.01      | ~ m1_pre_topc(sK4,sK1)
% 19.76/3.01      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 19.76/3.01      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 19.76/3.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 19.76/3.01      | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3))
% 19.76/3.01      | v2_struct_0(sK1)
% 19.76/3.01      | v2_struct_0(sK3)
% 19.76/3.01      | v2_struct_0(sK2)
% 19.76/3.01      | v2_struct_0(sK4)
% 19.76/3.01      | ~ l1_pre_topc(sK1)
% 19.76/3.01      | ~ l1_pre_topc(sK2)
% 19.76/3.01      | ~ v2_pre_topc(sK1)
% 19.76/3.01      | ~ v2_pre_topc(sK2) ),
% 19.76/3.01      inference(equality_resolution_simp,[status(thm)],[c_2242]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_35,negated_conjecture,
% 19.76/3.01      ( ~ v2_struct_0(sK1) ),
% 19.76/3.01      inference(cnf_transformation,[],[f64]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_29,negated_conjecture,
% 19.76/3.01      ( ~ v2_struct_0(sK3) ),
% 19.76/3.01      inference(cnf_transformation,[],[f70]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_20,negated_conjecture,
% 19.76/3.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 19.76/3.01      inference(cnf_transformation,[],[f79]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2333,plain,
% 19.76/3.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 19.76/3.01      | ~ m1_pre_topc(sK3,sK4)
% 19.76/3.01      | r1_tmap_1(sK4,sK2,sK5,sK7)
% 19.76/3.01      | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) ),
% 19.76/3.01      inference(global_propositional_subsumption,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_2243,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_27,c_26,
% 19.76/3.01                 c_23,c_20]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2334,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 19.76/3.01      | ~ m1_pre_topc(sK3,sK4)
% 19.76/3.01      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 19.76/3.01      | ~ r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) ),
% 19.76/3.01      inference(renaming,[status(thm)],[c_2333]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2335,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 19.76/3.01      | m1_pre_topc(sK3,sK4) != iProver_top
% 19.76/3.01      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_2334]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1001,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2010,plain,
% 19.76/3.01      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1001]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2313,plain,
% 19.76/3.01      ( X0 != sK7 | X0 = sK6 | sK6 != sK7 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_2010]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2591,plain,
% 19.76/3.01      ( sK7 != sK7 | sK7 = sK6 | sK6 != sK7 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_2313]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1004,plain,
% 19.76/3.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.76/3.01      theory(equality) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1954,plain,
% 19.76/3.01      ( m1_subset_1(X0,X1)
% 19.76/3.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 19.76/3.01      | X1 != u1_struct_0(sK4)
% 19.76/3.01      | X0 != sK6 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1004]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_3095,plain,
% 19.76/3.01      ( m1_subset_1(sK7,X0)
% 19.76/3.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 19.76/3.01      | X0 != u1_struct_0(sK4)
% 19.76/3.01      | sK7 != sK6 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1954]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_4044,plain,
% 19.76/3.01      ( m1_subset_1(sK7,u1_struct_0(sK4))
% 19.76/3.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 19.76/3.01      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 19.76/3.01      | sK7 != sK6 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_3095]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_4045,plain,
% 19.76/3.01      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 19.76/3.01      | sK7 != sK6
% 19.76/3.01      | m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top
% 19.76/3.01      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_4044]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_10355,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,sK7),u1_struct_0(sK3)) != iProver_top ),
% 19.76/3.01      inference(global_propositional_subsumption,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_5386,c_38,c_49,c_19,c_1881,c_1978,c_2335,c_2472,
% 19.76/3.01                 c_2591,c_3298,c_4045]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_10359,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
% 19.76/3.01      inference(superposition,[status(thm)],[c_19,c_10355]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_36,plain,
% 19.76/3.01      ( v2_struct_0(sK1) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_42,plain,
% 19.76/3.01      ( v2_struct_0(sK3) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_45,plain,
% 19.76/3.01      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_50,plain,
% 19.76/3.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_17,negated_conjecture,
% 19.76/3.01      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
% 19.76/3.01      inference(cnf_transformation,[],[f82]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_52,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1949,plain,
% 19.76/3.01      ( m1_subset_1(X0,X1)
% 19.76/3.01      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 19.76/3.01      | X1 != u1_struct_0(sK3)
% 19.76/3.01      | X0 != sK7 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1004]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1972,plain,
% 19.76/3.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 19.76/3.01      | m1_subset_1(sK6,X0)
% 19.76/3.01      | X0 != u1_struct_0(sK3)
% 19.76/3.01      | sK6 != sK7 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1949]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2109,plain,
% 19.76/3.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 19.76/3.01      | m1_subset_1(sK6,u1_struct_0(sK3))
% 19.76/3.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 19.76/3.01      | sK6 != sK7 ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1972]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2111,plain,
% 19.76/3.01      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 19.76/3.01      | sK6 != sK7
% 19.76/3.01      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 19.76/3.01      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2110,plain,
% 19.76/3.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_2794,plain,
% 19.76/3.01      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
% 19.76/3.01      inference(superposition,[status(thm)],[c_19,c_1775]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_5387,plain,
% 19.76/3.01      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 19.76/3.01      | m1_pre_topc(sK3,sK4) != iProver_top
% 19.76/3.01      | m1_pre_topc(sK4,sK1) != iProver_top
% 19.76/3.01      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 19.76/3.01      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 19.76/3.01      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top
% 19.76/3.01      | v2_struct_0(sK1) = iProver_top
% 19.76/3.01      | v2_struct_0(sK3) = iProver_top
% 19.76/3.01      | l1_pre_topc(sK1) != iProver_top
% 19.76/3.01      | v2_pre_topc(sK1) != iProver_top ),
% 19.76/3.01      inference(superposition,[status(thm)],[c_2794,c_5381]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_10362,plain,
% 19.76/3.01      ( r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
% 19.76/3.01      inference(global_propositional_subsumption,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_10359,c_36,c_37,c_38,c_42,c_45,c_49,c_50,c_19,c_52,
% 19.76/3.01                 c_2111,c_2110,c_2472,c_3298,c_5387]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_65614,plain,
% 19.76/3.01      ( r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 19.76/3.01      inference(superposition,[status(thm)],[c_64178,c_10362]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_65833,plain,
% 19.76/3.01      ( ~ r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
% 19.76/3.01      inference(predicate_to_equality_rev,[status(thm)],[c_65614]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(c_1928,plain,
% 19.76/3.01      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 19.76/3.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 19.76/3.01      | v2_struct_0(sK4)
% 19.76/3.01      | ~ l1_pre_topc(sK4)
% 19.76/3.01      | ~ v2_pre_topc(sK4) ),
% 19.76/3.01      inference(instantiation,[status(thm)],[c_577]) ).
% 19.76/3.01  
% 19.76/3.01  cnf(contradiction,plain,
% 19.76/3.01      ( $false ),
% 19.76/3.01      inference(minisat,
% 19.76/3.01                [status(thm)],
% 19.76/3.01                [c_66556,c_65833,c_3068,c_2469,c_1928,c_21,c_27,c_33,
% 19.76/3.01                 c_34]) ).
% 19.76/3.01  
% 19.76/3.01  
% 19.76/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.76/3.01  
% 19.76/3.01  ------                               Statistics
% 19.76/3.01  
% 19.76/3.01  ------ Selected
% 19.76/3.01  
% 19.76/3.01  total_time:                             2.257
% 19.76/3.01  
%------------------------------------------------------------------------------
