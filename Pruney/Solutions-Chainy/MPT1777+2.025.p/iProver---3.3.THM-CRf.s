%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:30 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 751 expanded)
%              Number of clauses        :  104 ( 161 expanded)
%              Number of leaves         :   22 ( 332 expanded)
%              Depth                    :   28
%              Number of atoms          : 1117 (10637 expanded)
%              Number of equality atoms :  278 (1597 expanded)
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

fof(f77,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f70,plain,(
    l1_pre_topc(sK1) ),
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

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f69,plain,(
    v2_pre_topc(sK1) ),
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

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1607,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

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

cnf(c_2824,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1621])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2910,plain,
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

cnf(c_3180,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | v1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2910,c_1623])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1605,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2825,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1621])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1619,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2840,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1619])).

cnf(c_3683,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3180,c_38,c_42,c_2825,c_2840])).

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

cnf(c_3379,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1616])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2896,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2901,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2896])).

cnf(c_3380,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1616])).

cnf(c_3524,plain,
    ( u1_struct_0(sK3) = X0
    | g1_pre_topc(X0,X1) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3379,c_38,c_2825,c_2901,c_3380])).

cnf(c_3525,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0 ),
    inference(renaming,[status(thm)],[c_3524])).

cnf(c_3688,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3683,c_3525])).

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

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

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

cnf(c_3022,plain,
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

cnf(c_3023,plain,
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
    inference(renaming,[status(thm)],[c_3022])).

cnf(c_3039,plain,
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
    inference(superposition,[status(thm)],[c_1661,c_3023])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

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

cnf(c_3104,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3039,c_36,c_37,c_38,c_42,c_45,c_49,c_52,c_1648])).

cnf(c_3714,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3688,c_3104])).

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

cnf(c_3206,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1597])).

cnf(c_3265,plain,
    ( m1_pre_topc(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3206,c_38,c_2825])).

cnf(c_3266,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3265])).

cnf(c_3273,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_3266])).

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
    inference(minisat,[status(thm)],[c_3714,c_3273,c_2825,c_2824,c_2795,c_1938,c_49,c_45,c_44,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:59:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.91/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/0.91  
% 2.91/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/0.91  
% 2.91/0.91  ------  iProver source info
% 2.91/0.91  
% 2.91/0.91  git: date: 2020-06-30 10:37:57 +0100
% 2.91/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/0.91  git: non_committed_changes: false
% 2.91/0.91  git: last_make_outside_of_git: false
% 2.91/0.91  
% 2.91/0.91  ------ 
% 2.91/0.91  
% 2.91/0.91  ------ Input Options
% 2.91/0.91  
% 2.91/0.91  --out_options                           all
% 2.91/0.91  --tptp_safe_out                         true
% 2.91/0.91  --problem_path                          ""
% 2.91/0.91  --include_path                          ""
% 2.91/0.91  --clausifier                            res/vclausify_rel
% 2.91/0.91  --clausifier_options                    --mode clausify
% 2.91/0.91  --stdin                                 false
% 2.91/0.91  --stats_out                             all
% 2.91/0.91  
% 2.91/0.91  ------ General Options
% 2.91/0.91  
% 2.91/0.91  --fof                                   false
% 2.91/0.91  --time_out_real                         305.
% 2.91/0.91  --time_out_virtual                      -1.
% 2.91/0.91  --symbol_type_check                     false
% 2.91/0.91  --clausify_out                          false
% 2.91/0.91  --sig_cnt_out                           false
% 2.91/0.91  --trig_cnt_out                          false
% 2.91/0.91  --trig_cnt_out_tolerance                1.
% 2.91/0.91  --trig_cnt_out_sk_spl                   false
% 2.91/0.91  --abstr_cl_out                          false
% 2.91/0.91  
% 2.91/0.91  ------ Global Options
% 2.91/0.91  
% 2.91/0.91  --schedule                              default
% 2.91/0.91  --add_important_lit                     false
% 2.91/0.91  --prop_solver_per_cl                    1000
% 2.91/0.91  --min_unsat_core                        false
% 2.91/0.91  --soft_assumptions                      false
% 2.91/0.91  --soft_lemma_size                       3
% 2.91/0.91  --prop_impl_unit_size                   0
% 2.91/0.91  --prop_impl_unit                        []
% 2.91/0.91  --share_sel_clauses                     true
% 2.91/0.91  --reset_solvers                         false
% 2.91/0.91  --bc_imp_inh                            [conj_cone]
% 2.91/0.91  --conj_cone_tolerance                   3.
% 2.91/0.91  --extra_neg_conj                        none
% 2.91/0.91  --large_theory_mode                     true
% 2.91/0.91  --prolific_symb_bound                   200
% 2.91/0.91  --lt_threshold                          2000
% 2.91/0.91  --clause_weak_htbl                      true
% 2.91/0.91  --gc_record_bc_elim                     false
% 2.91/0.91  
% 2.91/0.91  ------ Preprocessing Options
% 2.91/0.91  
% 2.91/0.91  --preprocessing_flag                    true
% 2.91/0.91  --time_out_prep_mult                    0.1
% 2.91/0.91  --splitting_mode                        input
% 2.91/0.91  --splitting_grd                         true
% 2.91/0.91  --splitting_cvd                         false
% 2.91/0.91  --splitting_cvd_svl                     false
% 2.91/0.91  --splitting_nvd                         32
% 2.91/0.91  --sub_typing                            true
% 2.91/0.91  --prep_gs_sim                           true
% 2.91/0.91  --prep_unflatten                        true
% 2.91/0.91  --prep_res_sim                          true
% 2.91/0.91  --prep_upred                            true
% 2.91/0.91  --prep_sem_filter                       exhaustive
% 2.91/0.91  --prep_sem_filter_out                   false
% 2.91/0.91  --pred_elim                             true
% 2.91/0.91  --res_sim_input                         true
% 2.91/0.91  --eq_ax_congr_red                       true
% 2.91/0.91  --pure_diseq_elim                       true
% 2.91/0.91  --brand_transform                       false
% 2.91/0.91  --non_eq_to_eq                          false
% 2.91/0.91  --prep_def_merge                        true
% 2.91/0.91  --prep_def_merge_prop_impl              false
% 2.91/0.91  --prep_def_merge_mbd                    true
% 2.91/0.91  --prep_def_merge_tr_red                 false
% 2.91/0.91  --prep_def_merge_tr_cl                  false
% 2.91/0.91  --smt_preprocessing                     true
% 2.91/0.91  --smt_ac_axioms                         fast
% 2.91/0.91  --preprocessed_out                      false
% 2.91/0.91  --preprocessed_stats                    false
% 2.91/0.91  
% 2.91/0.91  ------ Abstraction refinement Options
% 2.91/0.91  
% 2.91/0.91  --abstr_ref                             []
% 2.91/0.91  --abstr_ref_prep                        false
% 2.91/0.91  --abstr_ref_until_sat                   false
% 2.91/0.91  --abstr_ref_sig_restrict                funpre
% 2.91/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/0.91  --abstr_ref_under                       []
% 2.91/0.91  
% 2.91/0.91  ------ SAT Options
% 2.91/0.91  
% 2.91/0.91  --sat_mode                              false
% 2.91/0.91  --sat_fm_restart_options                ""
% 2.91/0.91  --sat_gr_def                            false
% 2.91/0.91  --sat_epr_types                         true
% 2.91/0.91  --sat_non_cyclic_types                  false
% 2.91/0.91  --sat_finite_models                     false
% 2.91/0.91  --sat_fm_lemmas                         false
% 2.91/0.91  --sat_fm_prep                           false
% 2.91/0.91  --sat_fm_uc_incr                        true
% 2.91/0.91  --sat_out_model                         small
% 2.91/0.91  --sat_out_clauses                       false
% 2.91/0.91  
% 2.91/0.91  ------ QBF Options
% 2.91/0.91  
% 2.91/0.91  --qbf_mode                              false
% 2.91/0.91  --qbf_elim_univ                         false
% 2.91/0.91  --qbf_dom_inst                          none
% 2.91/0.91  --qbf_dom_pre_inst                      false
% 2.91/0.91  --qbf_sk_in                             false
% 2.91/0.91  --qbf_pred_elim                         true
% 2.91/0.91  --qbf_split                             512
% 2.91/0.91  
% 2.91/0.91  ------ BMC1 Options
% 2.91/0.91  
% 2.91/0.91  --bmc1_incremental                      false
% 2.91/0.91  --bmc1_axioms                           reachable_all
% 2.91/0.91  --bmc1_min_bound                        0
% 2.91/0.91  --bmc1_max_bound                        -1
% 2.91/0.91  --bmc1_max_bound_default                -1
% 2.91/0.91  --bmc1_symbol_reachability              true
% 2.91/0.91  --bmc1_property_lemmas                  false
% 2.91/0.91  --bmc1_k_induction                      false
% 2.91/0.91  --bmc1_non_equiv_states                 false
% 2.91/0.91  --bmc1_deadlock                         false
% 2.91/0.91  --bmc1_ucm                              false
% 2.91/0.91  --bmc1_add_unsat_core                   none
% 2.91/0.91  --bmc1_unsat_core_children              false
% 2.91/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/0.91  --bmc1_out_stat                         full
% 2.91/0.91  --bmc1_ground_init                      false
% 2.91/0.91  --bmc1_pre_inst_next_state              false
% 2.91/0.91  --bmc1_pre_inst_state                   false
% 2.91/0.91  --bmc1_pre_inst_reach_state             false
% 2.91/0.91  --bmc1_out_unsat_core                   false
% 2.91/0.91  --bmc1_aig_witness_out                  false
% 2.91/0.91  --bmc1_verbose                          false
% 2.91/0.91  --bmc1_dump_clauses_tptp                false
% 2.91/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.91/0.91  --bmc1_dump_file                        -
% 2.91/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.91/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.91/0.91  --bmc1_ucm_extend_mode                  1
% 2.91/0.91  --bmc1_ucm_init_mode                    2
% 2.91/0.91  --bmc1_ucm_cone_mode                    none
% 2.91/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.91/0.91  --bmc1_ucm_relax_model                  4
% 2.91/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.91/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/0.91  --bmc1_ucm_layered_model                none
% 2.91/0.91  --bmc1_ucm_max_lemma_size               10
% 2.91/0.91  
% 2.91/0.91  ------ AIG Options
% 2.91/0.91  
% 2.91/0.91  --aig_mode                              false
% 2.91/0.91  
% 2.91/0.91  ------ Instantiation Options
% 2.91/0.91  
% 2.91/0.91  --instantiation_flag                    true
% 2.91/0.91  --inst_sos_flag                         false
% 2.91/0.91  --inst_sos_phase                        true
% 2.91/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/0.91  --inst_lit_sel_side                     num_symb
% 2.91/0.91  --inst_solver_per_active                1400
% 2.91/0.91  --inst_solver_calls_frac                1.
% 2.91/0.91  --inst_passive_queue_type               priority_queues
% 2.91/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/0.91  --inst_passive_queues_freq              [25;2]
% 2.91/0.91  --inst_dismatching                      true
% 2.91/0.91  --inst_eager_unprocessed_to_passive     true
% 2.91/0.91  --inst_prop_sim_given                   true
% 2.91/0.91  --inst_prop_sim_new                     false
% 2.91/0.91  --inst_subs_new                         false
% 2.91/0.91  --inst_eq_res_simp                      false
% 2.91/0.91  --inst_subs_given                       false
% 2.91/0.91  --inst_orphan_elimination               true
% 2.91/0.91  --inst_learning_loop_flag               true
% 2.91/0.91  --inst_learning_start                   3000
% 2.91/0.91  --inst_learning_factor                  2
% 2.91/0.91  --inst_start_prop_sim_after_learn       3
% 2.91/0.91  --inst_sel_renew                        solver
% 2.91/0.91  --inst_lit_activity_flag                true
% 2.91/0.91  --inst_restr_to_given                   false
% 2.91/0.91  --inst_activity_threshold               500
% 2.91/0.91  --inst_out_proof                        true
% 2.91/0.91  
% 2.91/0.91  ------ Resolution Options
% 2.91/0.91  
% 2.91/0.91  --resolution_flag                       true
% 2.91/0.91  --res_lit_sel                           adaptive
% 2.91/0.91  --res_lit_sel_side                      none
% 2.91/0.91  --res_ordering                          kbo
% 2.91/0.91  --res_to_prop_solver                    active
% 2.91/0.91  --res_prop_simpl_new                    false
% 2.91/0.91  --res_prop_simpl_given                  true
% 2.91/0.91  --res_passive_queue_type                priority_queues
% 2.91/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/0.91  --res_passive_queues_freq               [15;5]
% 2.91/0.91  --res_forward_subs                      full
% 2.91/0.91  --res_backward_subs                     full
% 2.91/0.91  --res_forward_subs_resolution           true
% 2.91/0.91  --res_backward_subs_resolution          true
% 2.91/0.91  --res_orphan_elimination                true
% 2.91/0.91  --res_time_limit                        2.
% 2.91/0.91  --res_out_proof                         true
% 2.91/0.91  
% 2.91/0.91  ------ Superposition Options
% 2.91/0.91  
% 2.91/0.91  --superposition_flag                    true
% 2.91/0.91  --sup_passive_queue_type                priority_queues
% 2.91/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.91/0.91  --demod_completeness_check              fast
% 2.91/0.91  --demod_use_ground                      true
% 2.91/0.91  --sup_to_prop_solver                    passive
% 2.91/0.91  --sup_prop_simpl_new                    true
% 2.91/0.91  --sup_prop_simpl_given                  true
% 2.91/0.91  --sup_fun_splitting                     false
% 2.91/0.91  --sup_smt_interval                      50000
% 2.91/0.91  
% 2.91/0.91  ------ Superposition Simplification Setup
% 2.91/0.91  
% 2.91/0.91  --sup_indices_passive                   []
% 2.91/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.91  --sup_full_bw                           [BwDemod]
% 2.91/0.91  --sup_immed_triv                        [TrivRules]
% 2.91/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.91  --sup_immed_bw_main                     []
% 2.91/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.91  
% 2.91/0.91  ------ Combination Options
% 2.91/0.91  
% 2.91/0.91  --comb_res_mult                         3
% 2.91/0.91  --comb_sup_mult                         2
% 2.91/0.91  --comb_inst_mult                        10
% 2.91/0.91  
% 2.91/0.91  ------ Debug Options
% 2.91/0.91  
% 2.91/0.91  --dbg_backtrace                         false
% 2.91/0.91  --dbg_dump_prop_clauses                 false
% 2.91/0.91  --dbg_dump_prop_clauses_file            -
% 2.91/0.91  --dbg_out_stat                          false
% 2.91/0.91  ------ Parsing...
% 2.91/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/0.91  
% 2.91/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.91/0.91  
% 2.91/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/0.91  
% 2.91/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.91/0.91  ------ Proving...
% 2.91/0.91  ------ Problem Properties 
% 2.91/0.91  
% 2.91/0.91  
% 2.91/0.91  clauses                                 32
% 2.91/0.91  conjectures                             17
% 2.91/0.91  EPR                                     16
% 2.91/0.91  Horn                                    28
% 2.91/0.91  unary                                   17
% 2.91/0.91  binary                                  2
% 2.91/0.91  lits                                    96
% 2.91/0.91  lits eq                                 11
% 2.91/0.91  fd_pure                                 0
% 2.91/0.91  fd_pseudo                               0
% 2.91/0.91  fd_cond                                 0
% 2.91/0.91  fd_pseudo_cond                          2
% 2.91/0.91  AC symbols                              0
% 2.91/0.91  
% 2.91/0.91  ------ Schedule dynamic 5 is on 
% 2.91/0.91  
% 2.91/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.91/0.91  
% 2.91/0.91  
% 2.91/0.91  ------ 
% 2.91/0.91  Current options:
% 2.91/0.91  ------ 
% 2.91/0.91  
% 2.91/0.91  ------ Input Options
% 2.91/0.91  
% 2.91/0.91  --out_options                           all
% 2.91/0.91  --tptp_safe_out                         true
% 2.91/0.91  --problem_path                          ""
% 2.91/0.91  --include_path                          ""
% 2.91/0.91  --clausifier                            res/vclausify_rel
% 2.91/0.91  --clausifier_options                    --mode clausify
% 2.91/0.91  --stdin                                 false
% 2.91/0.91  --stats_out                             all
% 2.91/0.91  
% 2.91/0.91  ------ General Options
% 2.91/0.91  
% 2.91/0.91  --fof                                   false
% 2.91/0.91  --time_out_real                         305.
% 2.91/0.91  --time_out_virtual                      -1.
% 2.91/0.91  --symbol_type_check                     false
% 2.91/0.91  --clausify_out                          false
% 2.91/0.91  --sig_cnt_out                           false
% 2.91/0.91  --trig_cnt_out                          false
% 2.91/0.91  --trig_cnt_out_tolerance                1.
% 2.91/0.91  --trig_cnt_out_sk_spl                   false
% 2.91/0.91  --abstr_cl_out                          false
% 2.91/0.91  
% 2.91/0.91  ------ Global Options
% 2.91/0.91  
% 2.91/0.91  --schedule                              default
% 2.91/0.91  --add_important_lit                     false
% 2.91/0.91  --prop_solver_per_cl                    1000
% 2.91/0.91  --min_unsat_core                        false
% 2.91/0.91  --soft_assumptions                      false
% 2.91/0.91  --soft_lemma_size                       3
% 2.91/0.91  --prop_impl_unit_size                   0
% 2.91/0.91  --prop_impl_unit                        []
% 2.91/0.91  --share_sel_clauses                     true
% 2.91/0.91  --reset_solvers                         false
% 2.91/0.91  --bc_imp_inh                            [conj_cone]
% 2.91/0.91  --conj_cone_tolerance                   3.
% 2.91/0.91  --extra_neg_conj                        none
% 2.91/0.91  --large_theory_mode                     true
% 2.91/0.91  --prolific_symb_bound                   200
% 2.91/0.91  --lt_threshold                          2000
% 2.91/0.91  --clause_weak_htbl                      true
% 2.91/0.91  --gc_record_bc_elim                     false
% 2.91/0.91  
% 2.91/0.91  ------ Preprocessing Options
% 2.91/0.91  
% 2.91/0.91  --preprocessing_flag                    true
% 2.91/0.91  --time_out_prep_mult                    0.1
% 2.91/0.91  --splitting_mode                        input
% 2.91/0.91  --splitting_grd                         true
% 2.91/0.91  --splitting_cvd                         false
% 2.91/0.91  --splitting_cvd_svl                     false
% 2.91/0.91  --splitting_nvd                         32
% 2.91/0.91  --sub_typing                            true
% 2.91/0.91  --prep_gs_sim                           true
% 2.91/0.91  --prep_unflatten                        true
% 2.91/0.91  --prep_res_sim                          true
% 2.91/0.91  --prep_upred                            true
% 2.91/0.91  --prep_sem_filter                       exhaustive
% 2.91/0.91  --prep_sem_filter_out                   false
% 2.91/0.91  --pred_elim                             true
% 2.91/0.91  --res_sim_input                         true
% 2.91/0.91  --eq_ax_congr_red                       true
% 2.91/0.91  --pure_diseq_elim                       true
% 2.91/0.91  --brand_transform                       false
% 2.91/0.91  --non_eq_to_eq                          false
% 2.91/0.91  --prep_def_merge                        true
% 2.91/0.91  --prep_def_merge_prop_impl              false
% 2.91/0.91  --prep_def_merge_mbd                    true
% 2.91/0.91  --prep_def_merge_tr_red                 false
% 2.91/0.91  --prep_def_merge_tr_cl                  false
% 2.91/0.91  --smt_preprocessing                     true
% 2.91/0.91  --smt_ac_axioms                         fast
% 2.91/0.91  --preprocessed_out                      false
% 2.91/0.91  --preprocessed_stats                    false
% 2.91/0.91  
% 2.91/0.91  ------ Abstraction refinement Options
% 2.91/0.91  
% 2.91/0.91  --abstr_ref                             []
% 2.91/0.91  --abstr_ref_prep                        false
% 2.91/0.91  --abstr_ref_until_sat                   false
% 2.91/0.91  --abstr_ref_sig_restrict                funpre
% 2.91/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/0.91  --abstr_ref_under                       []
% 2.91/0.91  
% 2.91/0.91  ------ SAT Options
% 2.91/0.91  
% 2.91/0.91  --sat_mode                              false
% 2.91/0.91  --sat_fm_restart_options                ""
% 2.91/0.91  --sat_gr_def                            false
% 2.91/0.91  --sat_epr_types                         true
% 2.91/0.91  --sat_non_cyclic_types                  false
% 2.91/0.91  --sat_finite_models                     false
% 2.91/0.91  --sat_fm_lemmas                         false
% 2.91/0.91  --sat_fm_prep                           false
% 2.91/0.91  --sat_fm_uc_incr                        true
% 2.91/0.91  --sat_out_model                         small
% 2.91/0.91  --sat_out_clauses                       false
% 2.91/0.91  
% 2.91/0.91  ------ QBF Options
% 2.91/0.91  
% 2.91/0.91  --qbf_mode                              false
% 2.91/0.91  --qbf_elim_univ                         false
% 2.91/0.91  --qbf_dom_inst                          none
% 2.91/0.91  --qbf_dom_pre_inst                      false
% 2.91/0.91  --qbf_sk_in                             false
% 2.91/0.91  --qbf_pred_elim                         true
% 2.91/0.91  --qbf_split                             512
% 2.91/0.91  
% 2.91/0.91  ------ BMC1 Options
% 2.91/0.91  
% 2.91/0.91  --bmc1_incremental                      false
% 2.91/0.91  --bmc1_axioms                           reachable_all
% 2.91/0.91  --bmc1_min_bound                        0
% 2.91/0.91  --bmc1_max_bound                        -1
% 2.91/0.91  --bmc1_max_bound_default                -1
% 2.91/0.91  --bmc1_symbol_reachability              true
% 2.91/0.91  --bmc1_property_lemmas                  false
% 2.91/0.91  --bmc1_k_induction                      false
% 2.91/0.91  --bmc1_non_equiv_states                 false
% 2.91/0.91  --bmc1_deadlock                         false
% 2.91/0.91  --bmc1_ucm                              false
% 2.91/0.91  --bmc1_add_unsat_core                   none
% 2.91/0.91  --bmc1_unsat_core_children              false
% 2.91/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/0.91  --bmc1_out_stat                         full
% 2.91/0.91  --bmc1_ground_init                      false
% 2.91/0.91  --bmc1_pre_inst_next_state              false
% 2.91/0.91  --bmc1_pre_inst_state                   false
% 2.91/0.91  --bmc1_pre_inst_reach_state             false
% 2.91/0.91  --bmc1_out_unsat_core                   false
% 2.91/0.91  --bmc1_aig_witness_out                  false
% 2.91/0.91  --bmc1_verbose                          false
% 2.91/0.91  --bmc1_dump_clauses_tptp                false
% 2.91/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.91/0.91  --bmc1_dump_file                        -
% 2.91/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.91/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.91/0.91  --bmc1_ucm_extend_mode                  1
% 2.91/0.91  --bmc1_ucm_init_mode                    2
% 2.91/0.91  --bmc1_ucm_cone_mode                    none
% 2.91/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.91/0.91  --bmc1_ucm_relax_model                  4
% 2.91/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.91/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/0.91  --bmc1_ucm_layered_model                none
% 2.91/0.91  --bmc1_ucm_max_lemma_size               10
% 2.91/0.91  
% 2.91/0.91  ------ AIG Options
% 2.91/0.91  
% 2.91/0.91  --aig_mode                              false
% 2.91/0.91  
% 2.91/0.91  ------ Instantiation Options
% 2.91/0.91  
% 2.91/0.91  --instantiation_flag                    true
% 2.91/0.91  --inst_sos_flag                         false
% 2.91/0.91  --inst_sos_phase                        true
% 2.91/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/0.91  --inst_lit_sel_side                     none
% 2.91/0.91  --inst_solver_per_active                1400
% 2.91/0.91  --inst_solver_calls_frac                1.
% 2.91/0.91  --inst_passive_queue_type               priority_queues
% 2.91/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/0.91  --inst_passive_queues_freq              [25;2]
% 2.91/0.91  --inst_dismatching                      true
% 2.91/0.91  --inst_eager_unprocessed_to_passive     true
% 2.91/0.91  --inst_prop_sim_given                   true
% 2.91/0.91  --inst_prop_sim_new                     false
% 2.91/0.91  --inst_subs_new                         false
% 2.91/0.91  --inst_eq_res_simp                      false
% 2.91/0.91  --inst_subs_given                       false
% 2.91/0.91  --inst_orphan_elimination               true
% 2.91/0.91  --inst_learning_loop_flag               true
% 2.91/0.91  --inst_learning_start                   3000
% 2.91/0.91  --inst_learning_factor                  2
% 2.91/0.91  --inst_start_prop_sim_after_learn       3
% 2.91/0.91  --inst_sel_renew                        solver
% 2.91/0.91  --inst_lit_activity_flag                true
% 2.91/0.91  --inst_restr_to_given                   false
% 2.91/0.91  --inst_activity_threshold               500
% 2.91/0.91  --inst_out_proof                        true
% 2.91/0.91  
% 2.91/0.91  ------ Resolution Options
% 2.91/0.91  
% 2.91/0.91  --resolution_flag                       false
% 2.91/0.91  --res_lit_sel                           adaptive
% 2.91/0.91  --res_lit_sel_side                      none
% 2.91/0.91  --res_ordering                          kbo
% 2.91/0.91  --res_to_prop_solver                    active
% 2.91/0.91  --res_prop_simpl_new                    false
% 2.91/0.91  --res_prop_simpl_given                  true
% 2.91/0.91  --res_passive_queue_type                priority_queues
% 2.91/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/0.91  --res_passive_queues_freq               [15;5]
% 2.91/0.91  --res_forward_subs                      full
% 2.91/0.91  --res_backward_subs                     full
% 2.91/0.91  --res_forward_subs_resolution           true
% 2.91/0.91  --res_backward_subs_resolution          true
% 2.91/0.91  --res_orphan_elimination                true
% 2.91/0.91  --res_time_limit                        2.
% 2.91/0.91  --res_out_proof                         true
% 2.91/0.91  
% 2.91/0.91  ------ Superposition Options
% 2.91/0.91  
% 2.91/0.91  --superposition_flag                    true
% 2.91/0.91  --sup_passive_queue_type                priority_queues
% 2.91/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.91/0.91  --demod_completeness_check              fast
% 2.91/0.91  --demod_use_ground                      true
% 2.91/0.91  --sup_to_prop_solver                    passive
% 2.91/0.91  --sup_prop_simpl_new                    true
% 2.91/0.91  --sup_prop_simpl_given                  true
% 2.91/0.91  --sup_fun_splitting                     false
% 2.91/0.91  --sup_smt_interval                      50000
% 2.91/0.91  
% 2.91/0.91  ------ Superposition Simplification Setup
% 2.91/0.91  
% 2.91/0.91  --sup_indices_passive                   []
% 2.91/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.91  --sup_full_bw                           [BwDemod]
% 2.91/0.91  --sup_immed_triv                        [TrivRules]
% 2.91/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.91  --sup_immed_bw_main                     []
% 2.91/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.91  
% 2.91/0.91  ------ Combination Options
% 2.91/0.91  
% 2.91/0.91  --comb_res_mult                         3
% 2.91/0.91  --comb_sup_mult                         2
% 2.91/0.91  --comb_inst_mult                        10
% 2.91/0.91  
% 2.91/0.91  ------ Debug Options
% 2.91/0.91  
% 2.91/0.91  --dbg_backtrace                         false
% 2.91/0.91  --dbg_dump_prop_clauses                 false
% 2.91/0.91  --dbg_dump_prop_clauses_file            -
% 2.91/0.91  --dbg_out_stat                          false
% 2.91/0.91  
% 2.91/0.91  
% 2.91/0.91  
% 2.91/0.91  
% 2.91/0.91  ------ Proving...
% 2.91/0.91  
% 2.91/0.91  
% 2.91/0.91  % SZS status Theorem for theBenchmark.p
% 2.91/0.91  
% 2.91/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/0.91  
% 2.91/0.91  fof(f14,conjecture,(
% 2.91/0.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f15,negated_conjecture,(
% 2.91/0.91    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.91/0.91    inference(negated_conjecture,[],[f14])).
% 2.91/0.91  
% 2.91/0.91  fof(f37,plain,(
% 2.91/0.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f15])).
% 2.91/0.91  
% 2.91/0.91  fof(f38,plain,(
% 2.91/0.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.91/0.91    inference(flattening,[],[f37])).
% 2.91/0.91  
% 2.91/0.91  fof(f49,plain,(
% 2.91/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f48,plain,(
% 2.91/0.91    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f47,plain,(
% 2.91/0.91    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK5,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f46,plain,(
% 2.91/0.91    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f45,plain,(
% 2.91/0.91    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f44,plain,(
% 2.91/0.91    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f43,plain,(
% 2.91/0.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f50,plain,(
% 2.91/0.91    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.91/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f38,f49,f48,f47,f46,f45,f44,f43])).
% 2.91/0.91  
% 2.91/0.91  fof(f77,plain,(
% 2.91/0.91    m1_pre_topc(sK4,sK1)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f4,axiom,(
% 2.91/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f22,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(ennf_transformation,[],[f4])).
% 2.91/0.91  
% 2.91/0.91  fof(f54,plain,(
% 2.91/0.91    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f22])).
% 2.91/0.91  
% 2.91/0.91  fof(f70,plain,(
% 2.91/0.91    l1_pre_topc(sK1)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f2,axiom,(
% 2.91/0.91    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f18,plain,(
% 2.91/0.91    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(ennf_transformation,[],[f2])).
% 2.91/0.91  
% 2.91/0.91  fof(f19,plain,(
% 2.91/0.91    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(flattening,[],[f18])).
% 2.91/0.91  
% 2.91/0.91  fof(f52,plain,(
% 2.91/0.91    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f19])).
% 2.91/0.91  
% 2.91/0.91  fof(f74,plain,(
% 2.91/0.91    ~v2_struct_0(sK3)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f75,plain,(
% 2.91/0.91    m1_pre_topc(sK3,sK1)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f81,plain,(
% 2.91/0.91    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f6,axiom,(
% 2.91/0.91    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f24,plain,(
% 2.91/0.91    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f6])).
% 2.91/0.91  
% 2.91/0.91  fof(f25,plain,(
% 2.91/0.91    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/0.91    inference(flattening,[],[f24])).
% 2.91/0.91  
% 2.91/0.91  fof(f57,plain,(
% 2.91/0.91    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f25])).
% 2.91/0.91  
% 2.91/0.91  fof(f7,axiom,(
% 2.91/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f26,plain,(
% 2.91/0.91    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.91/0.91    inference(ennf_transformation,[],[f7])).
% 2.91/0.91  
% 2.91/0.91  fof(f58,plain,(
% 2.91/0.91    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.91/0.91    inference(cnf_transformation,[],[f26])).
% 2.91/0.91  
% 2.91/0.91  fof(f5,axiom,(
% 2.91/0.91    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f23,plain,(
% 2.91/0.91    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(ennf_transformation,[],[f5])).
% 2.91/0.91  
% 2.91/0.91  fof(f55,plain,(
% 2.91/0.91    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f23])).
% 2.91/0.91  
% 2.91/0.91  fof(f85,plain,(
% 2.91/0.91    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f84,plain,(
% 2.91/0.91    sK6 = sK7),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f10,axiom,(
% 2.91/0.91    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f30,plain,(
% 2.91/0.91    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f10])).
% 2.91/0.91  
% 2.91/0.91  fof(f31,plain,(
% 2.91/0.91    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/0.91    inference(flattening,[],[f30])).
% 2.91/0.91  
% 2.91/0.91  fof(f40,plain,(
% 2.91/0.91    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.91/0.91    introduced(choice_axiom,[])).
% 2.91/0.91  
% 2.91/0.91  fof(f41,plain,(
% 2.91/0.91    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f40])).
% 2.91/0.91  
% 2.91/0.91  fof(f63,plain,(
% 2.91/0.91    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f41])).
% 2.91/0.91  
% 2.91/0.91  fof(f1,axiom,(
% 2.91/0.91    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f16,plain,(
% 2.91/0.91    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.91/0.91    inference(unused_predicate_definition_removal,[],[f1])).
% 2.91/0.91  
% 2.91/0.91  fof(f17,plain,(
% 2.91/0.91    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.91/0.91    inference(ennf_transformation,[],[f16])).
% 2.91/0.91  
% 2.91/0.91  fof(f51,plain,(
% 2.91/0.91    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.91/0.91    inference(cnf_transformation,[],[f17])).
% 2.91/0.91  
% 2.91/0.91  fof(f13,axiom,(
% 2.91/0.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f35,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f13])).
% 2.91/0.91  
% 2.91/0.91  fof(f36,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/0.91    inference(flattening,[],[f35])).
% 2.91/0.91  
% 2.91/0.91  fof(f42,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/0.91    inference(nnf_transformation,[],[f36])).
% 2.91/0.91  
% 2.91/0.91  fof(f67,plain,(
% 2.91/0.91    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f42])).
% 2.91/0.91  
% 2.91/0.91  fof(f87,plain,(
% 2.91/0.91    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/0.91    inference(equality_resolution,[],[f67])).
% 2.91/0.91  
% 2.91/0.91  fof(f79,plain,(
% 2.91/0.91    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f78,plain,(
% 2.91/0.91    v1_funct_1(sK5)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f12,axiom,(
% 2.91/0.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f33,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f12])).
% 2.91/0.91  
% 2.91/0.91  fof(f34,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/0.91    inference(flattening,[],[f33])).
% 2.91/0.91  
% 2.91/0.91  fof(f65,plain,(
% 2.91/0.91    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f34])).
% 2.91/0.91  
% 2.91/0.91  fof(f9,axiom,(
% 2.91/0.91    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f28,plain,(
% 2.91/0.91    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f9])).
% 2.91/0.91  
% 2.91/0.91  fof(f29,plain,(
% 2.91/0.91    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.91/0.91    inference(flattening,[],[f28])).
% 2.91/0.91  
% 2.91/0.91  fof(f62,plain,(
% 2.91/0.91    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f29])).
% 2.91/0.91  
% 2.91/0.91  fof(f3,axiom,(
% 2.91/0.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f20,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.91/0.91    inference(ennf_transformation,[],[f3])).
% 2.91/0.91  
% 2.91/0.91  fof(f21,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.91/0.91    inference(flattening,[],[f20])).
% 2.91/0.91  
% 2.91/0.91  fof(f53,plain,(
% 2.91/0.91    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f21])).
% 2.91/0.91  
% 2.91/0.91  fof(f71,plain,(
% 2.91/0.91    ~v2_struct_0(sK2)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f72,plain,(
% 2.91/0.91    v2_pre_topc(sK2)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f73,plain,(
% 2.91/0.91    l1_pre_topc(sK2)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f76,plain,(
% 2.91/0.91    ~v2_struct_0(sK4)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f80,plain,(
% 2.91/0.91    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f68,plain,(
% 2.91/0.91    ~v2_struct_0(sK1)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f69,plain,(
% 2.91/0.91    v2_pre_topc(sK1)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f82,plain,(
% 2.91/0.91    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f86,plain,(
% 2.91/0.91    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f83,plain,(
% 2.91/0.91    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.91/0.91    inference(cnf_transformation,[],[f50])).
% 2.91/0.91  
% 2.91/0.91  fof(f11,axiom,(
% 2.91/0.91    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f32,plain,(
% 2.91/0.91    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(ennf_transformation,[],[f11])).
% 2.91/0.91  
% 2.91/0.91  fof(f64,plain,(
% 2.91/0.91    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f32])).
% 2.91/0.91  
% 2.91/0.91  fof(f8,axiom,(
% 2.91/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.91/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.91  
% 2.91/0.91  fof(f27,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(ennf_transformation,[],[f8])).
% 2.91/0.91  
% 2.91/0.91  fof(f39,plain,(
% 2.91/0.91    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.91/0.91    inference(nnf_transformation,[],[f27])).
% 2.91/0.91  
% 2.91/0.91  fof(f60,plain,(
% 2.91/0.91    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.91/0.91    inference(cnf_transformation,[],[f39])).
% 2.91/0.91  
% 2.91/0.91  cnf(c_26,negated_conjecture,
% 2.91/0.91      ( m1_pre_topc(sK4,sK1) ),
% 2.91/0.91      inference(cnf_transformation,[],[f77]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1607,plain,
% 2.91/0.91      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_3,plain,
% 2.91/0.91      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.91/0.91      inference(cnf_transformation,[],[f54]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1621,plain,
% 2.91/0.91      ( m1_pre_topc(X0,X1) != iProver_top
% 2.91/0.91      | l1_pre_topc(X1) != iProver_top
% 2.91/0.91      | l1_pre_topc(X0) = iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_2824,plain,
% 2.91/0.91      ( l1_pre_topc(sK1) != iProver_top
% 2.91/0.91      | l1_pre_topc(sK4) = iProver_top ),
% 2.91/0.91      inference(superposition,[status(thm)],[c_1607,c_1621]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_33,negated_conjecture,
% 2.91/0.91      ( l1_pre_topc(sK1) ),
% 2.91/0.91      inference(cnf_transformation,[],[f70]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_38,plain,
% 2.91/0.91      ( l1_pre_topc(sK1) = iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_2910,plain,
% 2.91/0.91      ( l1_pre_topc(sK4) = iProver_top ),
% 2.91/0.91      inference(global_propositional_subsumption,
% 2.91/0.91                [status(thm)],
% 2.91/0.91                [c_2824,c_38]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1,plain,
% 2.91/0.91      ( ~ l1_pre_topc(X0)
% 2.91/0.91      | ~ v1_pre_topc(X0)
% 2.91/0.91      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.91/0.91      inference(cnf_transformation,[],[f52]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1623,plain,
% 2.91/0.91      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.91/0.91      | l1_pre_topc(X0) != iProver_top
% 2.91/0.91      | v1_pre_topc(X0) != iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_3180,plain,
% 2.91/0.91      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
% 2.91/0.91      | v1_pre_topc(sK4) != iProver_top ),
% 2.91/0.91      inference(superposition,[status(thm)],[c_2910,c_1623]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_29,negated_conjecture,
% 2.91/0.91      ( ~ v2_struct_0(sK3) ),
% 2.91/0.91      inference(cnf_transformation,[],[f74]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_42,plain,
% 2.91/0.91      ( v2_struct_0(sK3) != iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_28,negated_conjecture,
% 2.91/0.91      ( m1_pre_topc(sK3,sK1) ),
% 2.91/0.91      inference(cnf_transformation,[],[f75]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1605,plain,
% 2.91/0.91      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_2825,plain,
% 2.91/0.91      ( l1_pre_topc(sK1) != iProver_top
% 2.91/0.91      | l1_pre_topc(sK3) = iProver_top ),
% 2.91/0.91      inference(superposition,[status(thm)],[c_1605,c_1621]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_22,negated_conjecture,
% 2.91/0.91      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
% 2.91/0.91      inference(cnf_transformation,[],[f81]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_5,plain,
% 2.91/0.91      ( v2_struct_0(X0)
% 2.91/0.91      | ~ l1_pre_topc(X0)
% 2.91/0.91      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.91/0.91      inference(cnf_transformation,[],[f57]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1619,plain,
% 2.91/0.91      ( v2_struct_0(X0) = iProver_top
% 2.91/0.91      | l1_pre_topc(X0) != iProver_top
% 2.91/0.91      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_2840,plain,
% 2.91/0.91      ( v2_struct_0(sK3) = iProver_top
% 2.91/0.91      | l1_pre_topc(sK3) != iProver_top
% 2.91/0.91      | v1_pre_topc(sK4) = iProver_top ),
% 2.91/0.91      inference(superposition,[status(thm)],[c_22,c_1619]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_3683,plain,
% 2.91/0.91      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
% 2.91/0.91      inference(global_propositional_subsumption,
% 2.91/0.91                [status(thm)],
% 2.91/0.91                [c_3180,c_38,c_42,c_2825,c_2840]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_8,plain,
% 2.91/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.91/0.91      | X2 = X1
% 2.91/0.91      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.91/0.91      inference(cnf_transformation,[],[f58]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_1616,plain,
% 2.91/0.91      ( X0 = X1
% 2.91/0.91      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.91/0.91      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.91/0.91      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_3379,plain,
% 2.91/0.91      ( g1_pre_topc(X0,X1) != sK4
% 2.91/0.91      | u1_struct_0(sK3) = X0
% 2.91/0.91      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.91/0.91      inference(superposition,[status(thm)],[c_22,c_1616]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_4,plain,
% 2.91/0.91      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.91/0.91      | ~ l1_pre_topc(X0) ),
% 2.91/0.91      inference(cnf_transformation,[],[f55]) ).
% 2.91/0.91  
% 2.91/0.91  cnf(c_2896,plain,
% 2.91/0.91      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.91/0.92      | ~ l1_pre_topc(sK3) ),
% 2.91/0.92      inference(instantiation,[status(thm)],[c_4]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2901,plain,
% 2.91/0.92      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 2.91/0.92      | l1_pre_topc(sK3) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_2896]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3380,plain,
% 2.91/0.92      ( g1_pre_topc(X0,X1) != sK4
% 2.91/0.92      | u1_struct_0(sK3) = X0
% 2.91/0.92      | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 2.91/0.92      inference(superposition,[status(thm)],[c_22,c_1616]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3524,plain,
% 2.91/0.92      ( u1_struct_0(sK3) = X0 | g1_pre_topc(X0,X1) != sK4 ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_3379,c_38,c_2825,c_2901,c_3380]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3525,plain,
% 2.91/0.92      ( g1_pre_topc(X0,X1) != sK4 | u1_struct_0(sK3) = X0 ),
% 2.91/0.92      inference(renaming,[status(thm)],[c_3524]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3688,plain,
% 2.91/0.92      ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
% 2.91/0.92      inference(superposition,[status(thm)],[c_3683,c_3525]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_18,negated_conjecture,
% 2.91/0.92      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.91/0.92      inference(cnf_transformation,[],[f85]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1611,plain,
% 2.91/0.92      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_19,negated_conjecture,
% 2.91/0.92      ( sK6 = sK7 ),
% 2.91/0.92      inference(cnf_transformation,[],[f84]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1661,plain,
% 2.91/0.92      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
% 2.91/0.92      inference(light_normalisation,[status(thm)],[c_1611,c_19]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_12,plain,
% 2.91/0.92      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.91/0.92      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | ~ v2_pre_topc(X0)
% 2.91/0.92      | ~ l1_pre_topc(X0) ),
% 2.91/0.92      inference(cnf_transformation,[],[f63]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_0,plain,
% 2.91/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f51]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_15,plain,
% 2.91/0.92      ( r1_tmap_1(X0,X1,X2,X3)
% 2.91/0.92      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.91/0.92      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.91/0.92      | ~ m1_connsp_2(X6,X0,X3)
% 2.91/0.92      | ~ m1_pre_topc(X0,X5)
% 2.91/0.92      | ~ m1_pre_topc(X4,X0)
% 2.91/0.92      | ~ m1_pre_topc(X4,X5)
% 2.91/0.92      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.91/0.92      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.91/0.92      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.91/0.92      | ~ v1_funct_1(X2)
% 2.91/0.92      | v2_struct_0(X5)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X4)
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | ~ v2_pre_topc(X5)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X5)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f87]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_24,negated_conjecture,
% 2.91/0.92      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.91/0.92      inference(cnf_transformation,[],[f79]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_456,plain,
% 2.91/0.92      ( r1_tmap_1(X0,X1,X2,X3)
% 2.91/0.92      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.91/0.92      | ~ m1_connsp_2(X6,X0,X3)
% 2.91/0.92      | ~ m1_pre_topc(X0,X5)
% 2.91/0.92      | ~ m1_pre_topc(X4,X0)
% 2.91/0.92      | ~ m1_pre_topc(X4,X5)
% 2.91/0.92      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.91/0.92      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.91/0.92      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.91/0.92      | ~ v1_funct_1(X2)
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X5)
% 2.91/0.92      | v2_struct_0(X4)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X5)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X5)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.91/0.92      | sK5 != X2 ),
% 2.91/0.92      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_457,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_connsp_2(X5,X3,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_pre_topc(X0,X2)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.91/0.92      | ~ v1_funct_1(sK5)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(unflattening,[status(thm)],[c_456]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_25,negated_conjecture,
% 2.91/0.92      ( v1_funct_1(sK5) ),
% 2.91/0.92      inference(cnf_transformation,[],[f78]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_461,plain,
% 2.91/0.92      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_pre_topc(X0,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_connsp_2(X5,X3,X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_457,c_25]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_462,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_connsp_2(X5,X3,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_pre_topc(X0,X2)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(renaming,[status(thm)],[c_461]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_14,plain,
% 2.91/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.91/0.92      | ~ m1_pre_topc(X2,X0)
% 2.91/0.92      | m1_pre_topc(X2,X1)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f65]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_509,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_connsp_2(X5,X3,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(forward_subsumption_resolution,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_462,c_14]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_533,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_connsp_2(X5,X3,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | X5 != X6
% 2.91/0.92      | u1_struct_0(X0) != X7
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(resolution_lifted,[status(thm)],[c_0,c_509]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_534,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_connsp_2(X5,X3,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(unflattening,[status(thm)],[c_533]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_755,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | v2_struct_0(X6)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | ~ v2_pre_topc(X6)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X6)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | X3 != X6
% 2.91/0.92      | X4 != X5
% 2.91/0.92      | sK0(X6,X5) != X7
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(resolution_lifted,[status(thm)],[c_12,c_534]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_756,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
% 2.91/0.92      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ v2_pre_topc(X3)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X3)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(unflattening,[status(thm)],[c_755]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_11,plain,
% 2.91/0.92      ( ~ m1_connsp_2(X0,X1,X2)
% 2.91/0.92      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.91/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f62]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_667,plain,
% 2.91/0.92      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.91/0.92      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.91/0.92      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X3)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X3)
% 2.91/0.92      | X3 != X1
% 2.91/0.92      | X2 != X0
% 2.91/0.92      | sK0(X3,X2) != X4 ),
% 2.91/0.92      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_668,plain,
% 2.91/0.92      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.91/0.92      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(unflattening,[status(thm)],[c_667]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_781,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ v2_pre_topc(X3)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X3)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(forward_subsumption_resolution,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_756,c_668]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2,plain,
% 2.91/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | v2_pre_topc(X0)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f53]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_802,plain,
% 2.91/0.92      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.91/0.92      | r1_tmap_1(X3,X1,sK5,X4)
% 2.91/0.92      | ~ m1_pre_topc(X3,X2)
% 2.91/0.92      | ~ m1_pre_topc(X0,X3)
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.91/0.92      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.91/0.92      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.91/0.92      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.91/0.92      | v2_struct_0(X0)
% 2.91/0.92      | v2_struct_0(X1)
% 2.91/0.92      | v2_struct_0(X3)
% 2.91/0.92      | v2_struct_0(X2)
% 2.91/0.92      | ~ v2_pre_topc(X1)
% 2.91/0.92      | ~ v2_pre_topc(X2)
% 2.91/0.92      | ~ l1_pre_topc(X1)
% 2.91/0.92      | ~ l1_pre_topc(X2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.91/0.92      inference(forward_subsumption_resolution,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_781,c_3,c_2]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1594,plain,
% 2.91/0.92      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.91/0.92      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.91/0.92      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
% 2.91/0.92      | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
% 2.91/0.92      | m1_pre_topc(X1,X3) != iProver_top
% 2.91/0.92      | m1_pre_topc(X2,X1) != iProver_top
% 2.91/0.92      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.91/0.92      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(X1,X4),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 2.91/0.92      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.91/0.92      | v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_struct_0(X2) = iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | v2_struct_0(X3) = iProver_top
% 2.91/0.92      | v2_pre_topc(X0) != iProver_top
% 2.91/0.92      | v2_pre_topc(X3) != iProver_top
% 2.91/0.92      | l1_pre_topc(X0) != iProver_top
% 2.91/0.92      | l1_pre_topc(X3) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1994,plain,
% 2.91/0.92      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.91/0.92      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.91/0.92      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.91/0.92      | m1_pre_topc(X0,X2) != iProver_top
% 2.91/0.92      | m1_pre_topc(X1,X0) != iProver_top
% 2.91/0.92      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.91/0.92      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.91/0.92      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_struct_0(X2) = iProver_top
% 2.91/0.92      | v2_struct_0(sK2) = iProver_top
% 2.91/0.92      | v2_pre_topc(X2) != iProver_top
% 2.91/0.92      | v2_pre_topc(sK2) != iProver_top
% 2.91/0.92      | l1_pre_topc(X2) != iProver_top
% 2.91/0.92      | l1_pre_topc(sK2) != iProver_top ),
% 2.91/0.92      inference(equality_resolution,[status(thm)],[c_1594]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_32,negated_conjecture,
% 2.91/0.92      ( ~ v2_struct_0(sK2) ),
% 2.91/0.92      inference(cnf_transformation,[],[f71]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_39,plain,
% 2.91/0.92      ( v2_struct_0(sK2) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_31,negated_conjecture,
% 2.91/0.92      ( v2_pre_topc(sK2) ),
% 2.91/0.92      inference(cnf_transformation,[],[f72]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_40,plain,
% 2.91/0.92      ( v2_pre_topc(sK2) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_30,negated_conjecture,
% 2.91/0.92      ( l1_pre_topc(sK2) ),
% 2.91/0.92      inference(cnf_transformation,[],[f73]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_41,plain,
% 2.91/0.92      ( l1_pre_topc(sK2) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2508,plain,
% 2.91/0.92      ( l1_pre_topc(X2) != iProver_top
% 2.91/0.92      | v2_struct_0(X2) = iProver_top
% 2.91/0.92      | v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.91/0.92      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.91/0.92      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.91/0.92      | m1_pre_topc(X1,X0) != iProver_top
% 2.91/0.92      | m1_pre_topc(X0,X2) != iProver_top
% 2.91/0.92      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.91/0.92      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.91/0.92      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.91/0.92      | v2_pre_topc(X2) != iProver_top ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_1994,c_39,c_40,c_41]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2509,plain,
% 2.91/0.92      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.91/0.92      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.91/0.92      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.91/0.92      | m1_pre_topc(X0,X2) != iProver_top
% 2.91/0.92      | m1_pre_topc(X1,X0) != iProver_top
% 2.91/0.92      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.91/0.92      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.91/0.92      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_struct_0(X2) = iProver_top
% 2.91/0.92      | v2_pre_topc(X2) != iProver_top
% 2.91/0.92      | l1_pre_topc(X2) != iProver_top ),
% 2.91/0.92      inference(renaming,[status(thm)],[c_2508]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2526,plain,
% 2.91/0.92      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.91/0.92      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.91/0.92      | m1_pre_topc(X0,sK4) != iProver_top
% 2.91/0.92      | m1_pre_topc(sK4,X1) != iProver_top
% 2.91/0.92      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.91/0.92      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.91/0.92      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_struct_0(sK4) = iProver_top
% 2.91/0.92      | v2_pre_topc(X1) != iProver_top
% 2.91/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.91/0.92      inference(equality_resolution,[status(thm)],[c_2509]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_27,negated_conjecture,
% 2.91/0.92      ( ~ v2_struct_0(sK4) ),
% 2.91/0.92      inference(cnf_transformation,[],[f76]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_44,plain,
% 2.91/0.92      ( v2_struct_0(sK4) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_23,negated_conjecture,
% 2.91/0.92      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.91/0.92      inference(cnf_transformation,[],[f80]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_48,plain,
% 2.91/0.92      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3022,plain,
% 2.91/0.92      ( v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.91/0.92      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.91/0.92      | m1_pre_topc(X0,sK4) != iProver_top
% 2.91/0.92      | m1_pre_topc(sK4,X1) != iProver_top
% 2.91/0.92      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.91/0.92      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.91/0.92      | v2_pre_topc(X1) != iProver_top
% 2.91/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_2526,c_44,c_48]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3023,plain,
% 2.91/0.92      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.91/0.92      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.91/0.92      | m1_pre_topc(X0,sK4) != iProver_top
% 2.91/0.92      | m1_pre_topc(sK4,X1) != iProver_top
% 2.91/0.92      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.91/0.92      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.91/0.92      | v2_struct_0(X1) = iProver_top
% 2.91/0.92      | v2_struct_0(X0) = iProver_top
% 2.91/0.92      | v2_pre_topc(X1) != iProver_top
% 2.91/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.91/0.92      inference(renaming,[status(thm)],[c_3022]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3039,plain,
% 2.91/0.92      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.91/0.92      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.91/0.92      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.91/0.92      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.91/0.92      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.91/0.92      | v2_struct_0(sK1) = iProver_top
% 2.91/0.92      | v2_struct_0(sK3) = iProver_top
% 2.91/0.92      | v2_pre_topc(sK1) != iProver_top
% 2.91/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.91/0.92      inference(superposition,[status(thm)],[c_1661,c_3023]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_35,negated_conjecture,
% 2.91/0.92      ( ~ v2_struct_0(sK1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f68]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_36,plain,
% 2.91/0.92      ( v2_struct_0(sK1) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_34,negated_conjecture,
% 2.91/0.92      ( v2_pre_topc(sK1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f69]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_37,plain,
% 2.91/0.92      ( v2_pre_topc(sK1) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_45,plain,
% 2.91/0.92      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_21,negated_conjecture,
% 2.91/0.92      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.91/0.92      inference(cnf_transformation,[],[f82]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_49,plain,
% 2.91/0.92      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_17,negated_conjecture,
% 2.91/0.92      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
% 2.91/0.92      inference(cnf_transformation,[],[f86]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_52,plain,
% 2.91/0.92      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_20,negated_conjecture,
% 2.91/0.92      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.91/0.92      inference(cnf_transformation,[],[f83]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1610,plain,
% 2.91/0.92      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1648,plain,
% 2.91/0.92      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.91/0.92      inference(light_normalisation,[status(thm)],[c_1610,c_19]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3104,plain,
% 2.91/0.92      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_3039,c_36,c_37,c_38,c_42,c_45,c_49,c_52,c_1648]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3714,plain,
% 2.91/0.92      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.91/0.92      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.91/0.92      inference(demodulation,[status(thm)],[c_3688,c_3104]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_13,plain,
% 2.91/0.92      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.91/0.92      inference(cnf_transformation,[],[f64]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1614,plain,
% 2.91/0.92      ( m1_pre_topc(X0,X0) = iProver_top
% 2.91/0.92      | l1_pre_topc(X0) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_10,plain,
% 2.91/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.91/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.91/0.92      | ~ l1_pre_topc(X0)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(cnf_transformation,[],[f60]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_186,plain,
% 2.91/0.92      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.91/0.92      | ~ m1_pre_topc(X0,X1)
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_10,c_3]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_187,plain,
% 2.91/0.92      ( ~ m1_pre_topc(X0,X1)
% 2.91/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.91/0.92      | ~ l1_pre_topc(X1) ),
% 2.91/0.92      inference(renaming,[status(thm)],[c_186]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1597,plain,
% 2.91/0.92      ( m1_pre_topc(X0,X1) != iProver_top
% 2.91/0.92      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.91/0.92      | l1_pre_topc(X1) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3206,plain,
% 2.91/0.92      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.91/0.92      | m1_pre_topc(X0,sK4) = iProver_top
% 2.91/0.92      | l1_pre_topc(sK3) != iProver_top ),
% 2.91/0.92      inference(superposition,[status(thm)],[c_22,c_1597]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3265,plain,
% 2.91/0.92      ( m1_pre_topc(X0,sK4) = iProver_top
% 2.91/0.92      | m1_pre_topc(X0,sK3) != iProver_top ),
% 2.91/0.92      inference(global_propositional_subsumption,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_3206,c_38,c_2825]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3266,plain,
% 2.91/0.92      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.91/0.92      | m1_pre_topc(X0,sK4) = iProver_top ),
% 2.91/0.92      inference(renaming,[status(thm)],[c_3265]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_3273,plain,
% 2.91/0.92      ( m1_pre_topc(sK3,sK4) = iProver_top
% 2.91/0.92      | l1_pre_topc(sK3) != iProver_top ),
% 2.91/0.92      inference(superposition,[status(thm)],[c_1614,c_3266]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2271,plain,
% 2.91/0.92      ( ~ m1_pre_topc(sK4,X0)
% 2.91/0.92      | ~ v2_pre_topc(X0)
% 2.91/0.92      | v2_pre_topc(sK4)
% 2.91/0.92      | ~ l1_pre_topc(X0) ),
% 2.91/0.92      inference(instantiation,[status(thm)],[c_2]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2794,plain,
% 2.91/0.92      ( ~ m1_pre_topc(sK4,sK1)
% 2.91/0.92      | ~ v2_pre_topc(sK1)
% 2.91/0.92      | v2_pre_topc(sK4)
% 2.91/0.92      | ~ l1_pre_topc(sK1) ),
% 2.91/0.92      inference(instantiation,[status(thm)],[c_2271]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_2795,plain,
% 2.91/0.92      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.91/0.92      | v2_pre_topc(sK1) != iProver_top
% 2.91/0.92      | v2_pre_topc(sK4) = iProver_top
% 2.91/0.92      | l1_pre_topc(sK1) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1937,plain,
% 2.91/0.92      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.91/0.92      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.91/0.92      | v2_struct_0(sK4)
% 2.91/0.92      | ~ v2_pre_topc(sK4)
% 2.91/0.92      | ~ l1_pre_topc(sK4) ),
% 2.91/0.92      inference(instantiation,[status(thm)],[c_668]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(c_1938,plain,
% 2.91/0.92      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.91/0.92      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.91/0.92      | v2_struct_0(sK4) = iProver_top
% 2.91/0.92      | v2_pre_topc(sK4) != iProver_top
% 2.91/0.92      | l1_pre_topc(sK4) != iProver_top ),
% 2.91/0.92      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 2.91/0.92  
% 2.91/0.92  cnf(contradiction,plain,
% 2.91/0.92      ( $false ),
% 2.91/0.92      inference(minisat,
% 2.91/0.92                [status(thm)],
% 2.91/0.92                [c_3714,c_3273,c_2825,c_2824,c_2795,c_1938,c_49,c_45,
% 2.91/0.92                 c_44,c_38,c_37]) ).
% 2.91/0.92  
% 2.91/0.92  
% 2.91/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/0.92  
% 2.91/0.92  ------                               Statistics
% 2.91/0.92  
% 2.91/0.92  ------ General
% 2.91/0.92  
% 2.91/0.92  abstr_ref_over_cycles:                  0
% 2.91/0.92  abstr_ref_under_cycles:                 0
% 2.91/0.92  gc_basic_clause_elim:                   0
% 2.91/0.92  forced_gc_time:                         0
% 2.91/0.92  parsing_time:                           0.01
% 2.91/0.92  unif_index_cands_time:                  0.
% 2.91/0.92  unif_index_add_time:                    0.
% 2.91/0.92  orderings_time:                         0.
% 2.91/0.92  out_proof_time:                         0.012
% 2.91/0.92  total_time:                             0.152
% 2.91/0.92  num_of_symbols:                         56
% 2.91/0.92  num_of_terms:                           3735
% 2.91/0.92  
% 2.91/0.92  ------ Preprocessing
% 2.91/0.92  
% 2.91/0.92  num_of_splits:                          0
% 2.91/0.92  num_of_split_atoms:                     0
% 2.91/0.92  num_of_reused_defs:                     0
% 2.91/0.92  num_eq_ax_congr_red:                    9
% 2.91/0.92  num_of_sem_filtered_clauses:            1
% 2.91/0.92  num_of_subtypes:                        0
% 2.91/0.92  monotx_restored_types:                  0
% 2.91/0.92  sat_num_of_epr_types:                   0
% 2.91/0.92  sat_num_of_non_cyclic_types:            0
% 2.91/0.92  sat_guarded_non_collapsed_types:        0
% 2.91/0.92  num_pure_diseq_elim:                    0
% 2.91/0.92  simp_replaced_by:                       0
% 2.91/0.92  res_preprocessed:                       163
% 2.91/0.92  prep_upred:                             0
% 2.91/0.92  prep_unflattend:                        17
% 2.91/0.92  smt_new_axioms:                         0
% 2.91/0.92  pred_elim_cands:                        7
% 2.91/0.92  pred_elim:                              4
% 2.91/0.92  pred_elim_cl:                           4
% 2.91/0.92  pred_elim_cycles:                       7
% 2.91/0.92  merged_defs:                            0
% 2.91/0.92  merged_defs_ncl:                        0
% 2.91/0.92  bin_hyper_res:                          0
% 2.91/0.92  prep_cycles:                            4
% 2.91/0.92  pred_elim_time:                         0.02
% 2.91/0.92  splitting_time:                         0.
% 2.91/0.92  sem_filter_time:                        0.
% 2.91/0.92  monotx_time:                            0.
% 2.91/0.92  subtype_inf_time:                       0.
% 2.91/0.92  
% 2.91/0.92  ------ Problem properties
% 2.91/0.92  
% 2.91/0.92  clauses:                                32
% 2.91/0.92  conjectures:                            17
% 2.91/0.92  epr:                                    16
% 2.91/0.92  horn:                                   28
% 2.91/0.92  ground:                                 17
% 2.91/0.92  unary:                                  17
% 2.91/0.92  binary:                                 2
% 2.91/0.92  lits:                                   96
% 2.91/0.92  lits_eq:                                11
% 2.91/0.92  fd_pure:                                0
% 2.91/0.92  fd_pseudo:                              0
% 2.91/0.92  fd_cond:                                0
% 2.91/0.92  fd_pseudo_cond:                         2
% 2.91/0.92  ac_symbols:                             0
% 2.91/0.92  
% 2.91/0.92  ------ Propositional Solver
% 2.91/0.92  
% 2.91/0.92  prop_solver_calls:                      27
% 2.91/0.92  prop_fast_solver_calls:                 1414
% 2.91/0.92  smt_solver_calls:                       0
% 2.91/0.92  smt_fast_solver_calls:                  0
% 2.91/0.92  prop_num_of_clauses:                    1138
% 2.91/0.92  prop_preprocess_simplified:             4873
% 2.91/0.92  prop_fo_subsumed:                       29
% 2.91/0.92  prop_solver_time:                       0.
% 2.91/0.92  smt_solver_time:                        0.
% 2.91/0.92  smt_fast_solver_time:                   0.
% 2.91/0.92  prop_fast_solver_time:                  0.
% 2.91/0.92  prop_unsat_core_time:                   0.
% 2.91/0.92  
% 2.91/0.92  ------ QBF
% 2.91/0.92  
% 2.91/0.92  qbf_q_res:                              0
% 2.91/0.92  qbf_num_tautologies:                    0
% 2.91/0.92  qbf_prep_cycles:                        0
% 2.91/0.92  
% 2.91/0.92  ------ BMC1
% 2.91/0.92  
% 2.91/0.92  bmc1_current_bound:                     -1
% 2.91/0.92  bmc1_last_solved_bound:                 -1
% 2.91/0.92  bmc1_unsat_core_size:                   -1
% 2.91/0.92  bmc1_unsat_core_parents_size:           -1
% 2.91/0.92  bmc1_merge_next_fun:                    0
% 2.91/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.91/0.92  
% 2.91/0.92  ------ Instantiation
% 2.91/0.92  
% 2.91/0.92  inst_num_of_clauses:                    347
% 2.91/0.92  inst_num_in_passive:                    125
% 2.91/0.92  inst_num_in_active:                     206
% 2.91/0.92  inst_num_in_unprocessed:                16
% 2.91/0.92  inst_num_of_loops:                      220
% 2.91/0.92  inst_num_of_learning_restarts:          0
% 2.91/0.92  inst_num_moves_active_passive:          11
% 2.91/0.92  inst_lit_activity:                      0
% 2.91/0.92  inst_lit_activity_moves:                0
% 2.91/0.92  inst_num_tautologies:                   0
% 2.91/0.92  inst_num_prop_implied:                  0
% 2.91/0.92  inst_num_existing_simplified:           0
% 2.91/0.92  inst_num_eq_res_simplified:             0
% 2.91/0.92  inst_num_child_elim:                    0
% 2.91/0.92  inst_num_of_dismatching_blockings:      69
% 2.91/0.92  inst_num_of_non_proper_insts:           401
% 2.91/0.92  inst_num_of_duplicates:                 0
% 2.91/0.92  inst_inst_num_from_inst_to_res:         0
% 2.91/0.92  inst_dismatching_checking_time:         0.
% 2.91/0.92  
% 2.91/0.92  ------ Resolution
% 2.91/0.92  
% 2.91/0.92  res_num_of_clauses:                     0
% 2.91/0.92  res_num_in_passive:                     0
% 2.91/0.92  res_num_in_active:                      0
% 2.91/0.92  res_num_of_loops:                       167
% 2.91/0.92  res_forward_subset_subsumed:            22
% 2.91/0.92  res_backward_subset_subsumed:           2
% 2.91/0.92  res_forward_subsumed:                   0
% 2.91/0.92  res_backward_subsumed:                  0
% 2.91/0.92  res_forward_subsumption_resolution:     8
% 2.91/0.92  res_backward_subsumption_resolution:    0
% 2.91/0.92  res_clause_to_clause_subsumption:       207
% 2.91/0.92  res_orphan_elimination:                 0
% 2.91/0.92  res_tautology_del:                      41
% 2.91/0.92  res_num_eq_res_simplified:              0
% 2.91/0.92  res_num_sel_changes:                    0
% 2.91/0.92  res_moves_from_active_to_pass:          0
% 2.91/0.92  
% 2.91/0.92  ------ Superposition
% 2.91/0.92  
% 2.91/0.92  sup_time_total:                         0.
% 2.91/0.92  sup_time_generating:                    0.
% 2.91/0.92  sup_time_sim_full:                      0.
% 2.91/0.92  sup_time_sim_immed:                     0.
% 2.91/0.92  
% 2.91/0.92  sup_num_of_clauses:                     48
% 2.91/0.92  sup_num_in_active:                      39
% 2.91/0.92  sup_num_in_passive:                     9
% 2.91/0.92  sup_num_of_loops:                       43
% 2.91/0.92  sup_fw_superposition:                   15
% 2.91/0.92  sup_bw_superposition:                   9
% 2.91/0.92  sup_immediate_simplified:               5
% 2.91/0.92  sup_given_eliminated:                   0
% 2.91/0.92  comparisons_done:                       0
% 2.91/0.92  comparisons_avoided:                    0
% 2.91/0.92  
% 2.91/0.92  ------ Simplifications
% 2.91/0.92  
% 2.91/0.92  
% 2.91/0.92  sim_fw_subset_subsumed:                 4
% 2.91/0.92  sim_bw_subset_subsumed:                 3
% 2.91/0.92  sim_fw_subsumed:                        0
% 2.91/0.92  sim_bw_subsumed:                        0
% 2.91/0.92  sim_fw_subsumption_res:                 0
% 2.91/0.92  sim_bw_subsumption_res:                 0
% 2.91/0.92  sim_tautology_del:                      4
% 2.91/0.92  sim_eq_tautology_del:                   2
% 2.91/0.92  sim_eq_res_simp:                        0
% 2.91/0.92  sim_fw_demodulated:                     0
% 2.91/0.92  sim_bw_demodulated:                     4
% 2.91/0.92  sim_light_normalised:                   3
% 2.91/0.92  sim_joinable_taut:                      0
% 2.91/0.92  sim_joinable_simp:                      0
% 2.91/0.92  sim_ac_normalised:                      0
% 2.91/0.92  sim_smt_subsumption:                    0
% 2.91/0.92  
%------------------------------------------------------------------------------
