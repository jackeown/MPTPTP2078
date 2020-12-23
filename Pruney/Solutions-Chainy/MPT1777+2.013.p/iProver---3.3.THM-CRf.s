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
% DateTime   : Thu Dec  3 12:23:27 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  234 (5535 expanded)
%              Number of clauses        :  139 (1242 expanded)
%              Number of leaves         :   25 (2413 expanded)
%              Depth                    :   31
%              Number of atoms          : 1121 (73398 expanded)
%              Number of equality atoms :  367 (11222 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f45,f56,f55,f54,f53,f52,f51,f50])).

fof(f90,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f58,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f87,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1214,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1225,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_303,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_6])).

cnf(c_304,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_1204,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_3084,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1204])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1885,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

cnf(c_1886,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_3323,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3084,c_44,c_1886])).

cnf(c_3324,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3323])).

cnf(c_3331,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_3324])).

cnf(c_3435,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3331,c_44,c_1886])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1217,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1227,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1224,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1403,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1227,c_1224])).

cnf(c_5881,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1403])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_45,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_46,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_47,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_52,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_53,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6281,plain,
    ( l1_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5881,c_45,c_46,c_47,c_52,c_53])).

cnf(c_6282,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6281])).

cnf(c_6295,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3435,c_6282])).

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1232,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2984,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1236])).

cnf(c_2989,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_2984])).

cnf(c_1883,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

cnf(c_1884,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1883])).

cnf(c_3089,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2989,c_44,c_1884])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1239,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3886,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_1239])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1235,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2522,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1235])).

cnf(c_2889,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_2522])).

cnf(c_4441,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_44,c_1886,c_2889])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1230,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4118,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1230])).

cnf(c_2592,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2597,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2592])).

cnf(c_4119,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1230])).

cnf(c_4327,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(X0,X1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4118,c_44,c_1886,c_2597,c_4119])).

cnf(c_4328,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_4327])).

cnf(c_4446,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4441,c_4328])).

cnf(c_6301,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6295,c_4446])).

cnf(c_10,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1229,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4866,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4446,c_1229])).

cnf(c_4639,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4446,c_28])).

cnf(c_4870,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4866,c_4639])).

cnf(c_5560,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4870,c_44,c_1886])).

cnf(c_5561,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5560])).

cnf(c_5568,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_5561])).

cnf(c_5966,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5568,c_44,c_1884])).

cnf(c_5975,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5966,c_3324])).

cnf(c_6294,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK3,sK3,sK4)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5975,c_6282])).

cnf(c_8032,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5975,c_6294])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2860,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3231,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_32])).

cnf(c_1727,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1832,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_2859,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_4310,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK3)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_8278,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8032,c_40,c_39,c_38,c_37,c_36,c_33,c_31,c_30,c_29,c_1883,c_2860,c_3231,c_4310])).

cnf(c_13312,plain,
    ( k3_tmap_1(X0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6301,c_8278])).

cnf(c_13323,plain,
    ( k3_tmap_1(sK3,sK1,sK3,sK3,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_13312])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_42,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_43,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_13401,plain,
    ( k3_tmap_1(sK3,sK1,sK3,sK3,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13323,c_42,c_43,c_44])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1220,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1289,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1220,c_25])).

cnf(c_13404,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13401,c_1289])).

cnf(c_13324,plain,
    ( k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4)
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5975,c_13312])).

cnf(c_50,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3232,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3231])).

cnf(c_13917,plain,
    ( k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13324,c_43,c_44,c_50,c_1884,c_3232])).

cnf(c_21,plain,
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
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1223,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X5) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1473,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X5) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1223,c_1224])).

cnf(c_13920,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13917,c_1473])).

cnf(c_13973,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13920,c_4446])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_48,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2865,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2860])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1234,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3094,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_1234])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1237,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3335,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3094,c_1237])).

cnf(c_13,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1228,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3562,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3335,c_1228])).

cnf(c_6103,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_43,c_44,c_1884,c_3232])).

cnf(c_16,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_18,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_316,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_18])).

cnf(c_317,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_1203,plain,
    ( v1_tsep_1(X0,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_4653,plain,
    ( v1_tsep_1(sK2,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4446,c_1203])).

cnf(c_7670,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6103,c_4653])).

cnf(c_17186,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13973,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_52,c_53,c_54,c_1884,c_1886,c_2865,c_3232,c_3331,c_7670])).

cnf(c_17187,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17186])).

cnf(c_17195,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13404,c_17187])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_58,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_55,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17195,c_58,c_55])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:28:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.59/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.50  
% 7.59/1.50  ------  iProver source info
% 7.59/1.50  
% 7.59/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.50  git: non_committed_changes: false
% 7.59/1.50  git: last_make_outside_of_git: false
% 7.59/1.50  
% 7.59/1.50  ------ 
% 7.59/1.50  ------ Parsing...
% 7.59/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.50  ------ Proving...
% 7.59/1.50  ------ Problem Properties 
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  clauses                                 40
% 7.59/1.50  conjectures                             19
% 7.59/1.50  EPR                                     18
% 7.59/1.50  Horn                                    37
% 7.59/1.50  unary                                   19
% 7.59/1.50  binary                                  6
% 7.59/1.50  lits                                    125
% 7.59/1.50  lits eq                                 9
% 7.59/1.50  fd_pure                                 0
% 7.59/1.50  fd_pseudo                               0
% 7.59/1.50  fd_cond                                 0
% 7.59/1.50  fd_pseudo_cond                          2
% 7.59/1.50  AC symbols                              0
% 7.59/1.50  
% 7.59/1.50  ------ Input Options Time Limit: Unbounded
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  ------ 
% 7.59/1.50  Current options:
% 7.59/1.50  ------ 
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  ------ Proving...
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  % SZS status Theorem for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  fof(f18,conjecture,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f19,negated_conjecture,(
% 7.59/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.59/1.50    inference(negated_conjecture,[],[f18])).
% 7.59/1.50  
% 7.59/1.50  fof(f44,plain,(
% 7.59/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f19])).
% 7.59/1.50  
% 7.59/1.50  fof(f45,plain,(
% 7.59/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.59/1.50    inference(flattening,[],[f44])).
% 7.59/1.50  
% 7.59/1.50  fof(f56,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f55,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f54,plain,(
% 7.59/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f53,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f52,plain,(
% 7.59/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f51,plain,(
% 7.59/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f50,plain,(
% 7.59/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f57,plain,(
% 7.59/1.50    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.59/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f45,f56,f55,f54,f53,f52,f51,f50])).
% 7.59/1.50  
% 7.59/1.50  fof(f90,plain,(
% 7.59/1.50    m1_pre_topc(sK3,sK0)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f15,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f39,plain,(
% 7.59/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f15])).
% 7.59/1.50  
% 7.59/1.50  fof(f77,plain,(
% 7.59/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f39])).
% 7.59/1.50  
% 7.59/1.50  fof(f94,plain,(
% 7.59/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f10,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f31,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f10])).
% 7.59/1.50  
% 7.59/1.50  fof(f46,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(nnf_transformation,[],[f31])).
% 7.59/1.50  
% 7.59/1.50  fof(f69,plain,(
% 7.59/1.50    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f46])).
% 7.59/1.50  
% 7.59/1.50  fof(f6,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f27,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f6])).
% 7.59/1.50  
% 7.59/1.50  fof(f64,plain,(
% 7.59/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f27])).
% 7.59/1.50  
% 7.59/1.50  fof(f83,plain,(
% 7.59/1.50    l1_pre_topc(sK0)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f88,plain,(
% 7.59/1.50    m1_pre_topc(sK2,sK0)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f93,plain,(
% 7.59/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f12,axiom,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f34,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f12])).
% 7.59/1.50  
% 7.59/1.50  fof(f35,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.50    inference(flattening,[],[f34])).
% 7.59/1.50  
% 7.59/1.50  fof(f72,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f35])).
% 7.59/1.50  
% 7.59/1.50  fof(f16,axiom,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f40,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f16])).
% 7.59/1.50  
% 7.59/1.50  fof(f41,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.50    inference(flattening,[],[f40])).
% 7.59/1.50  
% 7.59/1.50  fof(f78,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f41])).
% 7.59/1.50  
% 7.59/1.50  fof(f84,plain,(
% 7.59/1.50    ~v2_struct_0(sK1)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f85,plain,(
% 7.59/1.50    v2_pre_topc(sK1)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f86,plain,(
% 7.59/1.50    l1_pre_topc(sK1)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f91,plain,(
% 7.59/1.50    v1_funct_1(sK4)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f92,plain,(
% 7.59/1.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f7,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f28,plain,(
% 7.59/1.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f7])).
% 7.59/1.50  
% 7.59/1.50  fof(f65,plain,(
% 7.59/1.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f28])).
% 7.59/1.50  
% 7.59/1.50  fof(f4,axiom,(
% 7.59/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f25,plain,(
% 7.59/1.50    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.59/1.50    inference(ennf_transformation,[],[f4])).
% 7.59/1.50  
% 7.59/1.50  fof(f62,plain,(
% 7.59/1.50    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f25])).
% 7.59/1.50  
% 7.59/1.50  fof(f1,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f20,plain,(
% 7.59/1.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f1])).
% 7.59/1.50  
% 7.59/1.50  fof(f21,plain,(
% 7.59/1.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(flattening,[],[f20])).
% 7.59/1.50  
% 7.59/1.50  fof(f58,plain,(
% 7.59/1.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f21])).
% 7.59/1.50  
% 7.59/1.50  fof(f61,plain,(
% 7.59/1.50    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f25])).
% 7.59/1.50  
% 7.59/1.50  fof(f8,axiom,(
% 7.59/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f29,plain,(
% 7.59/1.50    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.59/1.50    inference(ennf_transformation,[],[f8])).
% 7.59/1.50  
% 7.59/1.50  fof(f66,plain,(
% 7.59/1.50    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f29])).
% 7.59/1.50  
% 7.59/1.50  fof(f9,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f30,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f9])).
% 7.59/1.50  
% 7.59/1.50  fof(f68,plain,(
% 7.59/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f30])).
% 7.59/1.50  
% 7.59/1.50  fof(f82,plain,(
% 7.59/1.50    v2_pre_topc(sK0)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f89,plain,(
% 7.59/1.50    ~v2_struct_0(sK3)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f2,axiom,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f22,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f2])).
% 7.59/1.50  
% 7.59/1.50  fof(f23,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.50    inference(flattening,[],[f22])).
% 7.59/1.50  
% 7.59/1.50  fof(f59,plain,(
% 7.59/1.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f23])).
% 7.59/1.50  
% 7.59/1.50  fof(f81,plain,(
% 7.59/1.50    ~v2_struct_0(sK0)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f98,plain,(
% 7.59/1.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f97,plain,(
% 7.59/1.50    sK5 = sK6),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f17,axiom,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f42,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f17])).
% 7.59/1.50  
% 7.59/1.50  fof(f43,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.50    inference(flattening,[],[f42])).
% 7.59/1.50  
% 7.59/1.50  fof(f49,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.50    inference(nnf_transformation,[],[f43])).
% 7.59/1.50  
% 7.59/1.50  fof(f80,plain,(
% 7.59/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f49])).
% 7.59/1.50  
% 7.59/1.50  fof(f103,plain,(
% 7.59/1.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.50    inference(equality_resolution,[],[f80])).
% 7.59/1.50  
% 7.59/1.50  fof(f87,plain,(
% 7.59/1.50    ~v2_struct_0(sK2)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f5,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f26,plain,(
% 7.59/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f5])).
% 7.59/1.50  
% 7.59/1.50  fof(f63,plain,(
% 7.59/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f26])).
% 7.59/1.50  
% 7.59/1.50  fof(f3,axiom,(
% 7.59/1.50    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f24,plain,(
% 7.59/1.50    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f3])).
% 7.59/1.50  
% 7.59/1.50  fof(f60,plain,(
% 7.59/1.50    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f24])).
% 7.59/1.50  
% 7.59/1.50  fof(f11,axiom,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f32,plain,(
% 7.59/1.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f11])).
% 7.59/1.50  
% 7.59/1.50  fof(f33,plain,(
% 7.59/1.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.50    inference(flattening,[],[f32])).
% 7.59/1.50  
% 7.59/1.50  fof(f71,plain,(
% 7.59/1.50    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f33])).
% 7.59/1.50  
% 7.59/1.50  fof(f13,axiom,(
% 7.59/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f36,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.50    inference(ennf_transformation,[],[f13])).
% 7.59/1.50  
% 7.59/1.50  fof(f37,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.50    inference(flattening,[],[f36])).
% 7.59/1.50  
% 7.59/1.50  fof(f47,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.50    inference(nnf_transformation,[],[f37])).
% 7.59/1.50  
% 7.59/1.50  fof(f48,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.50    inference(flattening,[],[f47])).
% 7.59/1.50  
% 7.59/1.50  fof(f74,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f48])).
% 7.59/1.50  
% 7.59/1.50  fof(f101,plain,(
% 7.59/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.50    inference(equality_resolution,[],[f74])).
% 7.59/1.50  
% 7.59/1.50  fof(f14,axiom,(
% 7.59/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f38,plain,(
% 7.59/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f14])).
% 7.59/1.50  
% 7.59/1.50  fof(f76,plain,(
% 7.59/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f38])).
% 7.59/1.50  
% 7.59/1.50  fof(f99,plain,(
% 7.59/1.50    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  fof(f95,plain,(
% 7.59/1.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.59/1.50    inference(cnf_transformation,[],[f57])).
% 7.59/1.50  
% 7.59/1.50  cnf(c_32,negated_conjecture,
% 7.59/1.50      ( m1_pre_topc(sK3,sK0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1214,plain,
% 7.59/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_19,plain,
% 7.59/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1225,plain,
% 7.59/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_28,negated_conjecture,
% 7.59/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.59/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12,plain,
% 7.59/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.59/1.50      | ~ l1_pre_topc(X0)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6,plain,
% 7.59/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_303,plain,
% 7.59/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.59/1.50      | ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_12,c_6]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_304,plain,
% 7.59/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_303]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1204,plain,
% 7.59/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3084,plain,
% 7.59/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK3) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_28,c_1204]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_39,negated_conjecture,
% 7.59/1.50      ( l1_pre_topc(sK0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_44,plain,
% 7.59/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_34,negated_conjecture,
% 7.59/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1885,plain,
% 7.59/1.50      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_6,c_34]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1886,plain,
% 7.59/1.50      ( l1_pre_topc(sK0) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK2) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3323,plain,
% 7.59/1.50      ( m1_pre_topc(X0,sK3) = iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_3084,c_44,c_1886]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3324,plain,
% 7.59/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK3) = iProver_top ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_3323]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3331,plain,
% 7.59/1.50      ( m1_pre_topc(sK2,sK3) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1225,c_3324]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3435,plain,
% 7.59/1.50      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_3331,c_44,c_1886]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_29,negated_conjecture,
% 7.59/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.59/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1217,plain,
% 7.59/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_14,plain,
% 7.59/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.59/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.59/1.50      | ~ m1_pre_topc(X3,X1)
% 7.59/1.50      | ~ m1_pre_topc(X3,X4)
% 7.59/1.50      | ~ m1_pre_topc(X1,X4)
% 7.59/1.50      | v2_struct_0(X4)
% 7.59/1.50      | v2_struct_0(X2)
% 7.59/1.50      | ~ v1_funct_1(X0)
% 7.59/1.50      | ~ v2_pre_topc(X4)
% 7.59/1.50      | ~ v2_pre_topc(X2)
% 7.59/1.50      | ~ l1_pre_topc(X4)
% 7.59/1.50      | ~ l1_pre_topc(X2)
% 7.59/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1227,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 7.59/1.50      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.59/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.59/1.50      | m1_pre_topc(X3,X0) != iProver_top
% 7.59/1.50      | m1_pre_topc(X3,X4) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,X4) != iProver_top
% 7.59/1.50      | v2_struct_0(X4) = iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v1_funct_1(X2) != iProver_top
% 7.59/1.50      | v2_pre_topc(X4) != iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X4) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_20,plain,
% 7.59/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ m1_pre_topc(X2,X0)
% 7.59/1.50      | m1_pre_topc(X2,X1)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1224,plain,
% 7.59/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.59/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 7.59/1.50      | m1_pre_topc(X2,X1) = iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1403,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 7.59/1.50      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.59/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.59/1.50      | m1_pre_topc(X3,X0) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,X4) != iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v2_struct_0(X4) = iProver_top
% 7.59/1.50      | v1_funct_1(X2) != iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | v2_pre_topc(X4) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X4) != iProver_top ),
% 7.59/1.50      inference(forward_subsumption_resolution,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_1227,c_1224]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5881,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.59/1.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v2_struct_0(sK1) = iProver_top
% 7.59/1.50      | v1_funct_1(sK4) != iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1217,c_1403]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_38,negated_conjecture,
% 7.59/1.50      ( ~ v2_struct_0(sK1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_45,plain,
% 7.59/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_37,negated_conjecture,
% 7.59/1.50      ( v2_pre_topc(sK1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_46,plain,
% 7.59/1.50      ( v2_pre_topc(sK1) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_36,negated_conjecture,
% 7.59/1.50      ( l1_pre_topc(sK1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_47,plain,
% 7.59/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_31,negated_conjecture,
% 7.59/1.50      ( v1_funct_1(sK4) ),
% 7.59/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_52,plain,
% 7.59/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_30,negated_conjecture,
% 7.59/1.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_53,plain,
% 7.59/1.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6281,plain,
% 7.59/1.50      ( l1_pre_topc(X1) != iProver_top
% 7.59/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.59/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_5881,c_45,c_46,c_47,c_52,c_53]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6282,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.59/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_6281]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6295,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
% 7.59/1.50      | m1_pre_topc(sK3,X0) != iProver_top
% 7.59/1.50      | v2_struct_0(X0) = iProver_top
% 7.59/1.50      | v2_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_3435,c_6282]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_7,plain,
% 7.59/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.59/1.50      | ~ l1_pre_topc(X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1232,plain,
% 7.59/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3,plain,
% 7.59/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.59/1.50      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1236,plain,
% 7.59/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.59/1.50      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2984,plain,
% 7.59/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1232,c_1236]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2989,plain,
% 7.59/1.50      ( l1_pre_topc(sK2) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_28,c_2984]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1883,plain,
% 7.59/1.50      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_6,c_32]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1884,plain,
% 7.59/1.50      ( l1_pre_topc(sK0) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_1883]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3089,plain,
% 7.59/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_2989,c_44,c_1884]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_0,plain,
% 7.59/1.50      ( ~ l1_pre_topc(X0)
% 7.59/1.50      | ~ v1_pre_topc(X0)
% 7.59/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1239,plain,
% 7.59/1.50      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top
% 7.59/1.50      | v1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3886,plain,
% 7.59/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 7.59/1.50      | v1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_3089,c_1239]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4,plain,
% 7.59/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.59/1.50      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1235,plain,
% 7.59/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.59/1.50      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2522,plain,
% 7.59/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.59/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1232,c_1235]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2889,plain,
% 7.59/1.50      ( l1_pre_topc(sK2) != iProver_top
% 7.59/1.50      | v1_pre_topc(sK3) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_28,c_2522]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4441,plain,
% 7.59/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_3886,c_44,c_1886,c_2889]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_9,plain,
% 7.59/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.59/1.50      | X2 = X1
% 7.59/1.50      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1230,plain,
% 7.59/1.50      ( X0 = X1
% 7.59/1.50      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 7.59/1.50      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4118,plain,
% 7.59/1.50      ( g1_pre_topc(X0,X1) != sK3
% 7.59/1.50      | u1_struct_0(sK2) = X0
% 7.59/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_28,c_1230]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2592,plain,
% 7.59/1.50      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.59/1.50      | ~ l1_pre_topc(sK2) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2597,plain,
% 7.59/1.50      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_2592]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4119,plain,
% 7.59/1.50      ( g1_pre_topc(X0,X1) != sK3
% 7.59/1.50      | u1_struct_0(sK2) = X0
% 7.59/1.50      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_28,c_1230]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4327,plain,
% 7.59/1.50      ( u1_struct_0(sK2) = X0 | g1_pre_topc(X0,X1) != sK3 ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_4118,c_44,c_1886,c_2597,c_4119]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4328,plain,
% 7.59/1.50      ( g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0 ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_4327]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4446,plain,
% 7.59/1.50      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_4441,c_4328]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6301,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
% 7.59/1.50      | m1_pre_topc(sK3,X0) != iProver_top
% 7.59/1.50      | v2_struct_0(X0) = iProver_top
% 7.59/1.50      | v2_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_6295,c_4446]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10,plain,
% 7.59/1.50      ( m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1229,plain,
% 7.59/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 7.59/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4866,plain,
% 7.59/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK2))) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK2) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_4446,c_1229]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4639,plain,
% 7.59/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK2)) = sK3 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_4446,c_28]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4870,plain,
% 7.59/1.50      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_4866,c_4639]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5560,plain,
% 7.59/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_4870,c_44,c_1886]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5561,plain,
% 7.59/1.50      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.59/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_5560]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5568,plain,
% 7.59/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1225,c_5561]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5966,plain,
% 7.59/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_5568,c_44,c_1884]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5975,plain,
% 7.59/1.50      ( m1_pre_topc(sK3,sK3) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_5966,c_3324]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6294,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK3,sK3,sK4)
% 7.59/1.50      | m1_pre_topc(sK3,X0) != iProver_top
% 7.59/1.50      | v2_struct_0(X0) = iProver_top
% 7.59/1.50      | v2_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_5975,c_6282]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_8032,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4)
% 7.59/1.50      | v2_struct_0(sK3) = iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_5975,c_6294]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_40,negated_conjecture,
% 7.59/1.50      ( v2_pre_topc(sK0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_33,negated_conjecture,
% 7.59/1.50      ( ~ v2_struct_0(sK3) ),
% 7.59/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2860,plain,
% 7.59/1.50      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1,plain,
% 7.59/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | v2_pre_topc(X0)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3231,plain,
% 7.59/1.50      ( ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_1,c_32]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1727,plain,
% 7.59/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.59/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.59/1.50      | ~ m1_pre_topc(X2,X3)
% 7.59/1.50      | ~ m1_pre_topc(X2,X0)
% 7.59/1.50      | ~ m1_pre_topc(X0,X3)
% 7.59/1.50      | v2_struct_0(X1)
% 7.59/1.50      | v2_struct_0(X3)
% 7.59/1.50      | ~ v1_funct_1(sK4)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ v2_pre_topc(X3)
% 7.59/1.50      | ~ l1_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(X3)
% 7.59/1.50      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1832,plain,
% 7.59/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.59/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.59/1.50      | ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ m1_pre_topc(X0,sK3)
% 7.59/1.50      | ~ m1_pre_topc(sK3,X1)
% 7.59/1.50      | v2_struct_0(X1)
% 7.59/1.50      | v2_struct_0(sK1)
% 7.59/1.50      | ~ v1_funct_1(sK4)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ v2_pre_topc(sK1)
% 7.59/1.50      | ~ l1_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(sK1)
% 7.59/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_1727]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2859,plain,
% 7.59/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.59/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.59/1.50      | ~ m1_pre_topc(sK3,X0)
% 7.59/1.50      | ~ m1_pre_topc(sK3,sK3)
% 7.59/1.50      | v2_struct_0(X0)
% 7.59/1.50      | v2_struct_0(sK1)
% 7.59/1.50      | ~ v1_funct_1(sK4)
% 7.59/1.50      | ~ v2_pre_topc(X0)
% 7.59/1.50      | ~ v2_pre_topc(sK1)
% 7.59/1.50      | ~ l1_pre_topc(X0)
% 7.59/1.50      | ~ l1_pre_topc(sK1)
% 7.59/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK3,sK3,sK4) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_1832]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4310,plain,
% 7.59/1.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.59/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.59/1.50      | ~ m1_pre_topc(sK3,sK3)
% 7.59/1.50      | v2_struct_0(sK1)
% 7.59/1.50      | v2_struct_0(sK3)
% 7.59/1.50      | ~ v1_funct_1(sK4)
% 7.59/1.50      | ~ v2_pre_topc(sK1)
% 7.59/1.50      | ~ v2_pre_topc(sK3)
% 7.59/1.50      | ~ l1_pre_topc(sK1)
% 7.59/1.50      | ~ l1_pre_topc(sK3)
% 7.59/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_2859]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_8278,plain,
% 7.59/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_8032,c_40,c_39,c_38,c_37,c_36,c_33,c_31,c_30,c_29,
% 7.59/1.50                 c_1883,c_2860,c_3231,c_4310]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13312,plain,
% 7.59/1.50      ( k3_tmap_1(X0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4)
% 7.59/1.50      | m1_pre_topc(sK3,X0) != iProver_top
% 7.59/1.50      | v2_struct_0(X0) = iProver_top
% 7.59/1.50      | v2_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_6301,c_8278]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13323,plain,
% 7.59/1.50      ( k3_tmap_1(sK3,sK1,sK3,sK3,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 7.59/1.50      | v2_struct_0(sK0) = iProver_top
% 7.59/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1214,c_13312]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_41,negated_conjecture,
% 7.59/1.50      ( ~ v2_struct_0(sK0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_42,plain,
% 7.59/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_43,plain,
% 7.59/1.50      ( v2_pre_topc(sK0) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13401,plain,
% 7.59/1.50      ( k3_tmap_1(sK3,sK1,sK3,sK3,sK4) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_13323,c_42,c_43,c_44]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_24,negated_conjecture,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.59/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1220,plain,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_25,negated_conjecture,
% 7.59/1.50      ( sK5 = sK6 ),
% 7.59/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1289,plain,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_1220,c_25]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13404,plain,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),sK5) = iProver_top ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_13401,c_1289]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13324,plain,
% 7.59/1.50      ( k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4)
% 7.59/1.50      | v2_struct_0(sK3) = iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_5975,c_13312]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_50,plain,
% 7.59/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3232,plain,
% 7.59/1.50      ( v2_pre_topc(sK0) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_3231]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13917,plain,
% 7.59/1.50      ( k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK3,sK4) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_13324,c_43,c_44,c_50,c_1884,c_3232]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_21,plain,
% 7.59/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.59/1.50      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.59/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.59/1.50      | ~ v1_tsep_1(X4,X5)
% 7.59/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.59/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.59/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.59/1.50      | ~ m1_pre_topc(X4,X5)
% 7.59/1.50      | ~ m1_pre_topc(X4,X0)
% 7.59/1.50      | ~ m1_pre_topc(X0,X5)
% 7.59/1.50      | v2_struct_0(X1)
% 7.59/1.50      | v2_struct_0(X5)
% 7.59/1.50      | v2_struct_0(X0)
% 7.59/1.50      | v2_struct_0(X4)
% 7.59/1.50      | ~ v1_funct_1(X2)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ v2_pre_topc(X5)
% 7.59/1.50      | ~ l1_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(X5) ),
% 7.59/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1223,plain,
% 7.59/1.50      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 7.59/1.50      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 7.59/1.50      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.59/1.50      | v1_tsep_1(X4,X5) != iProver_top
% 7.59/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.59/1.50      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 7.59/1.50      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 7.59/1.50      | m1_pre_topc(X4,X5) != iProver_top
% 7.59/1.50      | m1_pre_topc(X4,X0) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,X5) != iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v2_struct_0(X5) = iProver_top
% 7.59/1.50      | v2_struct_0(X0) = iProver_top
% 7.59/1.50      | v2_struct_0(X4) = iProver_top
% 7.59/1.50      | v1_funct_1(X2) != iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | v2_pre_topc(X5) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X5) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1473,plain,
% 7.59/1.50      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 7.59/1.50      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 7.59/1.50      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.59/1.50      | v1_tsep_1(X4,X5) != iProver_top
% 7.59/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.59/1.50      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 7.59/1.50      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 7.59/1.50      | m1_pre_topc(X4,X0) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,X5) != iProver_top
% 7.59/1.50      | v2_struct_0(X1) = iProver_top
% 7.59/1.50      | v2_struct_0(X5) = iProver_top
% 7.59/1.50      | v2_struct_0(X0) = iProver_top
% 7.59/1.50      | v2_struct_0(X4) = iProver_top
% 7.59/1.50      | v1_funct_1(X2) != iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | v2_pre_topc(X5) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X5) != iProver_top ),
% 7.59/1.50      inference(forward_subsumption_resolution,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_1223,c_1224]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13920,plain,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top
% 7.59/1.50      | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
% 7.59/1.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.59/1.50      | v1_tsep_1(sK2,sK3) != iProver_top
% 7.59/1.50      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.59/1.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.59/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 7.59/1.50      | v2_struct_0(sK2) = iProver_top
% 7.59/1.50      | v2_struct_0(sK1) = iProver_top
% 7.59/1.50      | v2_struct_0(sK3) = iProver_top
% 7.59/1.50      | v1_funct_1(sK4) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_13917,c_1473]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13973,plain,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top
% 7.59/1.50      | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
% 7.59/1.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.59/1.50      | v1_tsep_1(sK2,sK3) != iProver_top
% 7.59/1.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.59/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 7.59/1.50      | v2_struct_0(sK2) = iProver_top
% 7.59/1.50      | v2_struct_0(sK1) = iProver_top
% 7.59/1.50      | v2_struct_0(sK3) = iProver_top
% 7.59/1.50      | v1_funct_1(sK4) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_13920,c_4446]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_35,negated_conjecture,
% 7.59/1.50      ( ~ v2_struct_0(sK2) ),
% 7.59/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_48,plain,
% 7.59/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_54,plain,
% 7.59/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2865,plain,
% 7.59/1.50      ( m1_pre_topc(sK3,sK3) = iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_2860]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5,plain,
% 7.59/1.50      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1234,plain,
% 7.59/1.50      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3094,plain,
% 7.59/1.50      ( l1_struct_0(sK3) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_3089,c_1234]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2,plain,
% 7.59/1.50      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1237,plain,
% 7.59/1.50      ( k2_struct_0(X0) = u1_struct_0(X0)
% 7.59/1.50      | l1_struct_0(X0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3335,plain,
% 7.59/1.50      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_3094,c_1237]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13,plain,
% 7.59/1.50      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.59/1.50      | ~ v2_pre_topc(X0)
% 7.59/1.50      | ~ l1_pre_topc(X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1228,plain,
% 7.59/1.50      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 7.59/1.50      | v2_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3562,plain,
% 7.59/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_3335,c_1228]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6103,plain,
% 7.59/1.50      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_3562,c_43,c_44,c_1884,c_3232]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_16,plain,
% 7.59/1.50      ( v1_tsep_1(X0,X1)
% 7.59/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.59/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.50      | ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_18,plain,
% 7.59/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.50      | ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_316,plain,
% 7.59/1.50      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.59/1.50      | v1_tsep_1(X0,X1)
% 7.59/1.50      | ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_16,c_18]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_317,plain,
% 7.59/1.50      ( v1_tsep_1(X0,X1)
% 7.59/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.59/1.50      | ~ m1_pre_topc(X0,X1)
% 7.59/1.50      | ~ v2_pre_topc(X1)
% 7.59/1.50      | ~ l1_pre_topc(X1) ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_316]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1203,plain,
% 7.59/1.50      ( v1_tsep_1(X0,X1) = iProver_top
% 7.59/1.50      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 7.59/1.50      | m1_pre_topc(X0,X1) != iProver_top
% 7.59/1.50      | v2_pre_topc(X1) != iProver_top
% 7.59/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4653,plain,
% 7.59/1.50      ( v1_tsep_1(sK2,X0) = iProver_top
% 7.59/1.50      | v3_pre_topc(u1_struct_0(sK3),X0) != iProver_top
% 7.59/1.50      | m1_pre_topc(sK2,X0) != iProver_top
% 7.59/1.50      | v2_pre_topc(X0) != iProver_top
% 7.59/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_4446,c_1203]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_7670,plain,
% 7.59/1.50      ( v1_tsep_1(sK2,sK3) = iProver_top
% 7.59/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.59/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.59/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_6103,c_4653]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_17186,plain,
% 7.59/1.50      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.59/1.50      | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
% 7.59/1.50      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_13973,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_52,c_53,
% 7.59/1.50                 c_54,c_1884,c_1886,c_2865,c_3232,c_3331,c_7670]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_17187,plain,
% 7.59/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK3,sK4),X0) != iProver_top
% 7.59/1.50      | r1_tmap_1(sK3,sK1,sK4,X0) = iProver_top
% 7.59/1.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.59/1.50      inference(renaming,[status(thm)],[c_17186]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_17195,plain,
% 7.59/1.50      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 7.59/1.50      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_13404,c_17187]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_23,negated_conjecture,
% 7.59/1.50      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.59/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_58,plain,
% 7.59/1.50      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_27,negated_conjecture,
% 7.59/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_55,plain,
% 7.59/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(contradiction,plain,
% 7.59/1.50      ( $false ),
% 7.59/1.50      inference(minisat,[status(thm)],[c_17195,c_58,c_55]) ).
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  ------                               Statistics
% 7.59/1.50  
% 7.59/1.50  ------ Selected
% 7.59/1.50  
% 7.59/1.50  total_time:                             0.518
% 7.59/1.50  
%------------------------------------------------------------------------------
