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
% DateTime   : Thu Dec  3 12:23:29 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  188 (1214 expanded)
%              Number of clauses        :  104 ( 255 expanded)
%              Number of leaves         :   22 ( 545 expanded)
%              Depth                    :   28
%              Number of atoms          : 1170 (17245 expanded)
%              Number of equality atoms :  302 (2635 expanded)
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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f50,plain,(
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
            ( ~ r1_tmap_1(X3,X1,X4,sK6)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f40,f50,f49,f48,f47,f46,f45,f44])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f53,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f51])).

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

fof(f58,plain,(
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

fof(f59,plain,(
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

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f41])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f52,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f43])).

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
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1567,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1576,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3783,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK1,sK3,sK3)
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1576])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1569,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1583,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2722,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1583])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2913,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2722,c_37])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1585,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3088,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | v1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_1585])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2723,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1583])).

cnf(c_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1581,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2840,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1581])).

cnf(c_3436,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3088,c_37,c_41,c_2723,c_2840])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1578,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3251,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1578])).

cnf(c_4,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3001,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3006,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3001])).

cnf(c_3252,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1578])).

cnf(c_3309,plain,
    ( u1_struct_0(sK3) = X0
    | g1_pre_topc(X0,X1) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3251,c_37,c_2723,c_3006,c_3252])).

cnf(c_3310,plain,
    ( g1_pre_topc(X0,X1) != sK4
    | u1_struct_0(sK3) = X0 ),
    inference(renaming,[status(thm)],[c_3309])).

cnf(c_3441,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3436,c_3310])).

cnf(c_3528,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3441,c_21])).

cnf(c_3789,plain,
    ( k1_tsep_1(sK1,sK3,sK3) = sK4
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3783,c_3441,c_3528])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4310,plain,
    ( k1_tsep_1(sK1,sK3,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3789,c_35,c_36,c_37,c_41])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1577,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4313,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4310,c_1577])).

cnf(c_17,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1573,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1619,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1573,c_18])).

cnf(c_10,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
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

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_442,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
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
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_443,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
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
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_447,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
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
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_24])).

cnf(c_448,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
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
    inference(renaming,[status(thm)],[c_447])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_495,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_448,c_13])).

cnf(c_519,plain,
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
    inference(resolution_lifted,[status(thm)],[c_0,c_495])).

cnf(c_520,plain,
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
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_741,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_520])).

cnf(c_742,plain,
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
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_653,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_767,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_742,c_654])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_788,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_767,c_3,c_2])).

cnf(c_1557,plain,
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
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2000,plain,
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
    inference(equality_resolution,[status(thm)],[c_1557])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2481,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2000,c_38,c_39,c_40])).

cnf(c_2482,plain,
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
    inference(renaming,[status(thm)],[c_2481])).

cnf(c_2499,plain,
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
    inference(equality_resolution,[status(thm)],[c_2482])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3009,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2499,c_43,c_47])).

cnf(c_3010,plain,
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
    inference(renaming,[status(thm)],[c_3009])).

cnf(c_3026,plain,
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
    inference(superposition,[status(thm)],[c_1619,c_3010])).

cnf(c_44,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1572,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1610,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1572,c_18])).

cnf(c_3029,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3026,c_35,c_36,c_37,c_41,c_44,c_48,c_51,c_1610])).

cnf(c_3526,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3441,c_3029])).

cnf(c_2315,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2924,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2925,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_1913,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_1914,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4313,c_3526,c_2925,c_2722,c_1914,c_48,c_44,c_43,c_42,c_41,c_37,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.53/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.05  
% 2.53/1.05  ------  iProver source info
% 2.53/1.05  
% 2.53/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.05  git: non_committed_changes: false
% 2.53/1.05  git: last_make_outside_of_git: false
% 2.53/1.05  
% 2.53/1.05  ------ 
% 2.53/1.05  
% 2.53/1.05  ------ Input Options
% 2.53/1.05  
% 2.53/1.05  --out_options                           all
% 2.53/1.05  --tptp_safe_out                         true
% 2.53/1.05  --problem_path                          ""
% 2.53/1.05  --include_path                          ""
% 2.53/1.05  --clausifier                            res/vclausify_rel
% 2.53/1.05  --clausifier_options                    --mode clausify
% 2.53/1.05  --stdin                                 false
% 2.53/1.05  --stats_out                             all
% 2.53/1.05  
% 2.53/1.05  ------ General Options
% 2.53/1.05  
% 2.53/1.05  --fof                                   false
% 2.53/1.05  --time_out_real                         305.
% 2.53/1.05  --time_out_virtual                      -1.
% 2.53/1.05  --symbol_type_check                     false
% 2.53/1.05  --clausify_out                          false
% 2.53/1.05  --sig_cnt_out                           false
% 2.53/1.05  --trig_cnt_out                          false
% 2.53/1.05  --trig_cnt_out_tolerance                1.
% 2.53/1.05  --trig_cnt_out_sk_spl                   false
% 2.53/1.05  --abstr_cl_out                          false
% 2.53/1.05  
% 2.53/1.05  ------ Global Options
% 2.53/1.05  
% 2.53/1.05  --schedule                              default
% 2.53/1.05  --add_important_lit                     false
% 2.53/1.05  --prop_solver_per_cl                    1000
% 2.53/1.05  --min_unsat_core                        false
% 2.53/1.05  --soft_assumptions                      false
% 2.53/1.05  --soft_lemma_size                       3
% 2.53/1.05  --prop_impl_unit_size                   0
% 2.53/1.05  --prop_impl_unit                        []
% 2.53/1.05  --share_sel_clauses                     true
% 2.53/1.05  --reset_solvers                         false
% 2.53/1.05  --bc_imp_inh                            [conj_cone]
% 2.53/1.05  --conj_cone_tolerance                   3.
% 2.53/1.05  --extra_neg_conj                        none
% 2.53/1.05  --large_theory_mode                     true
% 2.53/1.05  --prolific_symb_bound                   200
% 2.53/1.05  --lt_threshold                          2000
% 2.53/1.05  --clause_weak_htbl                      true
% 2.53/1.05  --gc_record_bc_elim                     false
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing Options
% 2.53/1.05  
% 2.53/1.05  --preprocessing_flag                    true
% 2.53/1.05  --time_out_prep_mult                    0.1
% 2.53/1.05  --splitting_mode                        input
% 2.53/1.05  --splitting_grd                         true
% 2.53/1.05  --splitting_cvd                         false
% 2.53/1.05  --splitting_cvd_svl                     false
% 2.53/1.05  --splitting_nvd                         32
% 2.53/1.05  --sub_typing                            true
% 2.53/1.05  --prep_gs_sim                           true
% 2.53/1.05  --prep_unflatten                        true
% 2.53/1.05  --prep_res_sim                          true
% 2.53/1.05  --prep_upred                            true
% 2.53/1.05  --prep_sem_filter                       exhaustive
% 2.53/1.05  --prep_sem_filter_out                   false
% 2.53/1.05  --pred_elim                             true
% 2.53/1.05  --res_sim_input                         true
% 2.53/1.05  --eq_ax_congr_red                       true
% 2.53/1.05  --pure_diseq_elim                       true
% 2.53/1.05  --brand_transform                       false
% 2.53/1.05  --non_eq_to_eq                          false
% 2.53/1.05  --prep_def_merge                        true
% 2.53/1.05  --prep_def_merge_prop_impl              false
% 2.53/1.05  --prep_def_merge_mbd                    true
% 2.53/1.05  --prep_def_merge_tr_red                 false
% 2.53/1.05  --prep_def_merge_tr_cl                  false
% 2.53/1.05  --smt_preprocessing                     true
% 2.53/1.05  --smt_ac_axioms                         fast
% 2.53/1.05  --preprocessed_out                      false
% 2.53/1.05  --preprocessed_stats                    false
% 2.53/1.05  
% 2.53/1.05  ------ Abstraction refinement Options
% 2.53/1.05  
% 2.53/1.05  --abstr_ref                             []
% 2.53/1.05  --abstr_ref_prep                        false
% 2.53/1.05  --abstr_ref_until_sat                   false
% 2.53/1.05  --abstr_ref_sig_restrict                funpre
% 2.53/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.05  --abstr_ref_under                       []
% 2.53/1.05  
% 2.53/1.05  ------ SAT Options
% 2.53/1.05  
% 2.53/1.05  --sat_mode                              false
% 2.53/1.05  --sat_fm_restart_options                ""
% 2.53/1.05  --sat_gr_def                            false
% 2.53/1.05  --sat_epr_types                         true
% 2.53/1.05  --sat_non_cyclic_types                  false
% 2.53/1.05  --sat_finite_models                     false
% 2.53/1.05  --sat_fm_lemmas                         false
% 2.53/1.05  --sat_fm_prep                           false
% 2.53/1.05  --sat_fm_uc_incr                        true
% 2.53/1.05  --sat_out_model                         small
% 2.53/1.05  --sat_out_clauses                       false
% 2.53/1.05  
% 2.53/1.05  ------ QBF Options
% 2.53/1.05  
% 2.53/1.05  --qbf_mode                              false
% 2.53/1.05  --qbf_elim_univ                         false
% 2.53/1.05  --qbf_dom_inst                          none
% 2.53/1.05  --qbf_dom_pre_inst                      false
% 2.53/1.05  --qbf_sk_in                             false
% 2.53/1.05  --qbf_pred_elim                         true
% 2.53/1.05  --qbf_split                             512
% 2.53/1.05  
% 2.53/1.05  ------ BMC1 Options
% 2.53/1.05  
% 2.53/1.05  --bmc1_incremental                      false
% 2.53/1.05  --bmc1_axioms                           reachable_all
% 2.53/1.05  --bmc1_min_bound                        0
% 2.53/1.05  --bmc1_max_bound                        -1
% 2.53/1.05  --bmc1_max_bound_default                -1
% 2.53/1.05  --bmc1_symbol_reachability              true
% 2.53/1.05  --bmc1_property_lemmas                  false
% 2.53/1.05  --bmc1_k_induction                      false
% 2.53/1.05  --bmc1_non_equiv_states                 false
% 2.53/1.05  --bmc1_deadlock                         false
% 2.53/1.05  --bmc1_ucm                              false
% 2.53/1.05  --bmc1_add_unsat_core                   none
% 2.53/1.05  --bmc1_unsat_core_children              false
% 2.53/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.05  --bmc1_out_stat                         full
% 2.53/1.05  --bmc1_ground_init                      false
% 2.53/1.05  --bmc1_pre_inst_next_state              false
% 2.53/1.05  --bmc1_pre_inst_state                   false
% 2.53/1.05  --bmc1_pre_inst_reach_state             false
% 2.53/1.05  --bmc1_out_unsat_core                   false
% 2.53/1.05  --bmc1_aig_witness_out                  false
% 2.53/1.05  --bmc1_verbose                          false
% 2.53/1.05  --bmc1_dump_clauses_tptp                false
% 2.53/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.05  --bmc1_dump_file                        -
% 2.53/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.05  --bmc1_ucm_extend_mode                  1
% 2.53/1.05  --bmc1_ucm_init_mode                    2
% 2.53/1.05  --bmc1_ucm_cone_mode                    none
% 2.53/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.05  --bmc1_ucm_relax_model                  4
% 2.53/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.05  --bmc1_ucm_layered_model                none
% 2.53/1.05  --bmc1_ucm_max_lemma_size               10
% 2.53/1.05  
% 2.53/1.05  ------ AIG Options
% 2.53/1.05  
% 2.53/1.05  --aig_mode                              false
% 2.53/1.05  
% 2.53/1.05  ------ Instantiation Options
% 2.53/1.05  
% 2.53/1.05  --instantiation_flag                    true
% 2.53/1.05  --inst_sos_flag                         false
% 2.53/1.05  --inst_sos_phase                        true
% 2.53/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel_side                     num_symb
% 2.53/1.05  --inst_solver_per_active                1400
% 2.53/1.05  --inst_solver_calls_frac                1.
% 2.53/1.05  --inst_passive_queue_type               priority_queues
% 2.53/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.05  --inst_passive_queues_freq              [25;2]
% 2.53/1.05  --inst_dismatching                      true
% 2.53/1.05  --inst_eager_unprocessed_to_passive     true
% 2.53/1.05  --inst_prop_sim_given                   true
% 2.53/1.05  --inst_prop_sim_new                     false
% 2.53/1.05  --inst_subs_new                         false
% 2.53/1.05  --inst_eq_res_simp                      false
% 2.53/1.05  --inst_subs_given                       false
% 2.53/1.05  --inst_orphan_elimination               true
% 2.53/1.05  --inst_learning_loop_flag               true
% 2.53/1.05  --inst_learning_start                   3000
% 2.53/1.05  --inst_learning_factor                  2
% 2.53/1.05  --inst_start_prop_sim_after_learn       3
% 2.53/1.05  --inst_sel_renew                        solver
% 2.53/1.05  --inst_lit_activity_flag                true
% 2.53/1.05  --inst_restr_to_given                   false
% 2.53/1.05  --inst_activity_threshold               500
% 2.53/1.05  --inst_out_proof                        true
% 2.53/1.05  
% 2.53/1.05  ------ Resolution Options
% 2.53/1.05  
% 2.53/1.05  --resolution_flag                       true
% 2.53/1.05  --res_lit_sel                           adaptive
% 2.53/1.05  --res_lit_sel_side                      none
% 2.53/1.05  --res_ordering                          kbo
% 2.53/1.05  --res_to_prop_solver                    active
% 2.53/1.05  --res_prop_simpl_new                    false
% 2.53/1.05  --res_prop_simpl_given                  true
% 2.53/1.05  --res_passive_queue_type                priority_queues
% 2.53/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.05  --res_passive_queues_freq               [15;5]
% 2.53/1.05  --res_forward_subs                      full
% 2.53/1.05  --res_backward_subs                     full
% 2.53/1.05  --res_forward_subs_resolution           true
% 2.53/1.05  --res_backward_subs_resolution          true
% 2.53/1.05  --res_orphan_elimination                true
% 2.53/1.05  --res_time_limit                        2.
% 2.53/1.05  --res_out_proof                         true
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Options
% 2.53/1.05  
% 2.53/1.05  --superposition_flag                    true
% 2.53/1.05  --sup_passive_queue_type                priority_queues
% 2.53/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.05  --demod_completeness_check              fast
% 2.53/1.05  --demod_use_ground                      true
% 2.53/1.05  --sup_to_prop_solver                    passive
% 2.53/1.05  --sup_prop_simpl_new                    true
% 2.53/1.05  --sup_prop_simpl_given                  true
% 2.53/1.05  --sup_fun_splitting                     false
% 2.53/1.05  --sup_smt_interval                      50000
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Simplification Setup
% 2.53/1.05  
% 2.53/1.05  --sup_indices_passive                   []
% 2.53/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_full_bw                           [BwDemod]
% 2.53/1.05  --sup_immed_triv                        [TrivRules]
% 2.53/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_immed_bw_main                     []
% 2.53/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  
% 2.53/1.05  ------ Combination Options
% 2.53/1.05  
% 2.53/1.05  --comb_res_mult                         3
% 2.53/1.05  --comb_sup_mult                         2
% 2.53/1.05  --comb_inst_mult                        10
% 2.53/1.05  
% 2.53/1.05  ------ Debug Options
% 2.53/1.05  
% 2.53/1.05  --dbg_backtrace                         false
% 2.53/1.05  --dbg_dump_prop_clauses                 false
% 2.53/1.05  --dbg_dump_prop_clauses_file            -
% 2.53/1.05  --dbg_out_stat                          false
% 2.53/1.05  ------ Parsing...
% 2.53/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.05  ------ Proving...
% 2.53/1.05  ------ Problem Properties 
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  clauses                                 31
% 2.53/1.05  conjectures                             17
% 2.53/1.05  EPR                                     15
% 2.53/1.05  Horn                                    25
% 2.53/1.05  unary                                   17
% 2.53/1.05  binary                                  1
% 2.53/1.05  lits                                    101
% 2.53/1.05  lits eq                                 12
% 2.53/1.05  fd_pure                                 0
% 2.53/1.05  fd_pseudo                               0
% 2.53/1.05  fd_cond                                 0
% 2.53/1.05  fd_pseudo_cond                          2
% 2.53/1.05  AC symbols                              0
% 2.53/1.05  
% 2.53/1.05  ------ Schedule dynamic 5 is on 
% 2.53/1.05  
% 2.53/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  ------ 
% 2.53/1.05  Current options:
% 2.53/1.05  ------ 
% 2.53/1.05  
% 2.53/1.05  ------ Input Options
% 2.53/1.05  
% 2.53/1.05  --out_options                           all
% 2.53/1.05  --tptp_safe_out                         true
% 2.53/1.05  --problem_path                          ""
% 2.53/1.05  --include_path                          ""
% 2.53/1.05  --clausifier                            res/vclausify_rel
% 2.53/1.05  --clausifier_options                    --mode clausify
% 2.53/1.05  --stdin                                 false
% 2.53/1.05  --stats_out                             all
% 2.53/1.05  
% 2.53/1.05  ------ General Options
% 2.53/1.05  
% 2.53/1.05  --fof                                   false
% 2.53/1.05  --time_out_real                         305.
% 2.53/1.05  --time_out_virtual                      -1.
% 2.53/1.05  --symbol_type_check                     false
% 2.53/1.05  --clausify_out                          false
% 2.53/1.05  --sig_cnt_out                           false
% 2.53/1.05  --trig_cnt_out                          false
% 2.53/1.05  --trig_cnt_out_tolerance                1.
% 2.53/1.05  --trig_cnt_out_sk_spl                   false
% 2.53/1.05  --abstr_cl_out                          false
% 2.53/1.05  
% 2.53/1.05  ------ Global Options
% 2.53/1.05  
% 2.53/1.05  --schedule                              default
% 2.53/1.05  --add_important_lit                     false
% 2.53/1.05  --prop_solver_per_cl                    1000
% 2.53/1.05  --min_unsat_core                        false
% 2.53/1.05  --soft_assumptions                      false
% 2.53/1.05  --soft_lemma_size                       3
% 2.53/1.05  --prop_impl_unit_size                   0
% 2.53/1.05  --prop_impl_unit                        []
% 2.53/1.05  --share_sel_clauses                     true
% 2.53/1.05  --reset_solvers                         false
% 2.53/1.05  --bc_imp_inh                            [conj_cone]
% 2.53/1.05  --conj_cone_tolerance                   3.
% 2.53/1.05  --extra_neg_conj                        none
% 2.53/1.05  --large_theory_mode                     true
% 2.53/1.05  --prolific_symb_bound                   200
% 2.53/1.05  --lt_threshold                          2000
% 2.53/1.05  --clause_weak_htbl                      true
% 2.53/1.05  --gc_record_bc_elim                     false
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing Options
% 2.53/1.05  
% 2.53/1.05  --preprocessing_flag                    true
% 2.53/1.05  --time_out_prep_mult                    0.1
% 2.53/1.05  --splitting_mode                        input
% 2.53/1.05  --splitting_grd                         true
% 2.53/1.05  --splitting_cvd                         false
% 2.53/1.05  --splitting_cvd_svl                     false
% 2.53/1.05  --splitting_nvd                         32
% 2.53/1.05  --sub_typing                            true
% 2.53/1.05  --prep_gs_sim                           true
% 2.53/1.05  --prep_unflatten                        true
% 2.53/1.05  --prep_res_sim                          true
% 2.53/1.05  --prep_upred                            true
% 2.53/1.05  --prep_sem_filter                       exhaustive
% 2.53/1.05  --prep_sem_filter_out                   false
% 2.53/1.05  --pred_elim                             true
% 2.53/1.05  --res_sim_input                         true
% 2.53/1.05  --eq_ax_congr_red                       true
% 2.53/1.05  --pure_diseq_elim                       true
% 2.53/1.05  --brand_transform                       false
% 2.53/1.05  --non_eq_to_eq                          false
% 2.53/1.05  --prep_def_merge                        true
% 2.53/1.05  --prep_def_merge_prop_impl              false
% 2.53/1.05  --prep_def_merge_mbd                    true
% 2.53/1.05  --prep_def_merge_tr_red                 false
% 2.53/1.05  --prep_def_merge_tr_cl                  false
% 2.53/1.05  --smt_preprocessing                     true
% 2.53/1.05  --smt_ac_axioms                         fast
% 2.53/1.05  --preprocessed_out                      false
% 2.53/1.05  --preprocessed_stats                    false
% 2.53/1.05  
% 2.53/1.05  ------ Abstraction refinement Options
% 2.53/1.05  
% 2.53/1.05  --abstr_ref                             []
% 2.53/1.05  --abstr_ref_prep                        false
% 2.53/1.05  --abstr_ref_until_sat                   false
% 2.53/1.05  --abstr_ref_sig_restrict                funpre
% 2.53/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.05  --abstr_ref_under                       []
% 2.53/1.05  
% 2.53/1.05  ------ SAT Options
% 2.53/1.05  
% 2.53/1.05  --sat_mode                              false
% 2.53/1.05  --sat_fm_restart_options                ""
% 2.53/1.05  --sat_gr_def                            false
% 2.53/1.05  --sat_epr_types                         true
% 2.53/1.05  --sat_non_cyclic_types                  false
% 2.53/1.05  --sat_finite_models                     false
% 2.53/1.05  --sat_fm_lemmas                         false
% 2.53/1.05  --sat_fm_prep                           false
% 2.53/1.05  --sat_fm_uc_incr                        true
% 2.53/1.05  --sat_out_model                         small
% 2.53/1.05  --sat_out_clauses                       false
% 2.53/1.05  
% 2.53/1.05  ------ QBF Options
% 2.53/1.05  
% 2.53/1.05  --qbf_mode                              false
% 2.53/1.05  --qbf_elim_univ                         false
% 2.53/1.05  --qbf_dom_inst                          none
% 2.53/1.05  --qbf_dom_pre_inst                      false
% 2.53/1.05  --qbf_sk_in                             false
% 2.53/1.05  --qbf_pred_elim                         true
% 2.53/1.05  --qbf_split                             512
% 2.53/1.05  
% 2.53/1.05  ------ BMC1 Options
% 2.53/1.05  
% 2.53/1.05  --bmc1_incremental                      false
% 2.53/1.05  --bmc1_axioms                           reachable_all
% 2.53/1.05  --bmc1_min_bound                        0
% 2.53/1.05  --bmc1_max_bound                        -1
% 2.53/1.05  --bmc1_max_bound_default                -1
% 2.53/1.05  --bmc1_symbol_reachability              true
% 2.53/1.05  --bmc1_property_lemmas                  false
% 2.53/1.05  --bmc1_k_induction                      false
% 2.53/1.05  --bmc1_non_equiv_states                 false
% 2.53/1.05  --bmc1_deadlock                         false
% 2.53/1.05  --bmc1_ucm                              false
% 2.53/1.05  --bmc1_add_unsat_core                   none
% 2.53/1.05  --bmc1_unsat_core_children              false
% 2.53/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.05  --bmc1_out_stat                         full
% 2.53/1.05  --bmc1_ground_init                      false
% 2.53/1.05  --bmc1_pre_inst_next_state              false
% 2.53/1.05  --bmc1_pre_inst_state                   false
% 2.53/1.05  --bmc1_pre_inst_reach_state             false
% 2.53/1.05  --bmc1_out_unsat_core                   false
% 2.53/1.05  --bmc1_aig_witness_out                  false
% 2.53/1.05  --bmc1_verbose                          false
% 2.53/1.05  --bmc1_dump_clauses_tptp                false
% 2.53/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.05  --bmc1_dump_file                        -
% 2.53/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.05  --bmc1_ucm_extend_mode                  1
% 2.53/1.05  --bmc1_ucm_init_mode                    2
% 2.53/1.05  --bmc1_ucm_cone_mode                    none
% 2.53/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.05  --bmc1_ucm_relax_model                  4
% 2.53/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.05  --bmc1_ucm_layered_model                none
% 2.53/1.05  --bmc1_ucm_max_lemma_size               10
% 2.53/1.05  
% 2.53/1.05  ------ AIG Options
% 2.53/1.05  
% 2.53/1.05  --aig_mode                              false
% 2.53/1.05  
% 2.53/1.05  ------ Instantiation Options
% 2.53/1.05  
% 2.53/1.05  --instantiation_flag                    true
% 2.53/1.05  --inst_sos_flag                         false
% 2.53/1.05  --inst_sos_phase                        true
% 2.53/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel_side                     none
% 2.53/1.05  --inst_solver_per_active                1400
% 2.53/1.05  --inst_solver_calls_frac                1.
% 2.53/1.05  --inst_passive_queue_type               priority_queues
% 2.53/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.05  --inst_passive_queues_freq              [25;2]
% 2.53/1.05  --inst_dismatching                      true
% 2.53/1.05  --inst_eager_unprocessed_to_passive     true
% 2.53/1.05  --inst_prop_sim_given                   true
% 2.53/1.05  --inst_prop_sim_new                     false
% 2.53/1.05  --inst_subs_new                         false
% 2.53/1.05  --inst_eq_res_simp                      false
% 2.53/1.05  --inst_subs_given                       false
% 2.53/1.05  --inst_orphan_elimination               true
% 2.53/1.05  --inst_learning_loop_flag               true
% 2.53/1.05  --inst_learning_start                   3000
% 2.53/1.05  --inst_learning_factor                  2
% 2.53/1.05  --inst_start_prop_sim_after_learn       3
% 2.53/1.05  --inst_sel_renew                        solver
% 2.53/1.05  --inst_lit_activity_flag                true
% 2.53/1.05  --inst_restr_to_given                   false
% 2.53/1.05  --inst_activity_threshold               500
% 2.53/1.05  --inst_out_proof                        true
% 2.53/1.05  
% 2.53/1.05  ------ Resolution Options
% 2.53/1.05  
% 2.53/1.05  --resolution_flag                       false
% 2.53/1.05  --res_lit_sel                           adaptive
% 2.53/1.05  --res_lit_sel_side                      none
% 2.53/1.05  --res_ordering                          kbo
% 2.53/1.05  --res_to_prop_solver                    active
% 2.53/1.05  --res_prop_simpl_new                    false
% 2.53/1.05  --res_prop_simpl_given                  true
% 2.53/1.05  --res_passive_queue_type                priority_queues
% 2.53/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.05  --res_passive_queues_freq               [15;5]
% 2.53/1.05  --res_forward_subs                      full
% 2.53/1.05  --res_backward_subs                     full
% 2.53/1.05  --res_forward_subs_resolution           true
% 2.53/1.05  --res_backward_subs_resolution          true
% 2.53/1.05  --res_orphan_elimination                true
% 2.53/1.05  --res_time_limit                        2.
% 2.53/1.05  --res_out_proof                         true
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Options
% 2.53/1.05  
% 2.53/1.05  --superposition_flag                    true
% 2.53/1.05  --sup_passive_queue_type                priority_queues
% 2.53/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.05  --demod_completeness_check              fast
% 2.53/1.05  --demod_use_ground                      true
% 2.53/1.05  --sup_to_prop_solver                    passive
% 2.53/1.05  --sup_prop_simpl_new                    true
% 2.53/1.05  --sup_prop_simpl_given                  true
% 2.53/1.05  --sup_fun_splitting                     false
% 2.53/1.05  --sup_smt_interval                      50000
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Simplification Setup
% 2.53/1.05  
% 2.53/1.05  --sup_indices_passive                   []
% 2.53/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_full_bw                           [BwDemod]
% 2.53/1.05  --sup_immed_triv                        [TrivRules]
% 2.53/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_immed_bw_main                     []
% 2.53/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  
% 2.53/1.05  ------ Combination Options
% 2.53/1.05  
% 2.53/1.05  --comb_res_mult                         3
% 2.53/1.05  --comb_sup_mult                         2
% 2.53/1.05  --comb_inst_mult                        10
% 2.53/1.05  
% 2.53/1.05  ------ Debug Options
% 2.53/1.05  
% 2.53/1.05  --dbg_backtrace                         false
% 2.53/1.05  --dbg_dump_prop_clauses                 false
% 2.53/1.05  --dbg_dump_prop_clauses_file            -
% 2.53/1.05  --dbg_out_stat                          false
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  ------ Proving...
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  % SZS status Theorem for theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  fof(f14,conjecture,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f15,negated_conjecture,(
% 2.53/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.53/1.05    inference(negated_conjecture,[],[f14])).
% 2.53/1.05  
% 2.53/1.05  fof(f39,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f15])).
% 2.53/1.05  
% 2.53/1.05  fof(f40,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f39])).
% 2.53/1.05  
% 2.53/1.05  fof(f50,plain,(
% 2.53/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f49,plain,(
% 2.53/1.05    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f48,plain,(
% 2.53/1.05    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK5,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f47,plain,(
% 2.53/1.05    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f46,plain,(
% 2.53/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f45,plain,(
% 2.53/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f44,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f51,plain,(
% 2.53/1.05    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.53/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f40,f50,f49,f48,f47,f46,f45,f44])).
% 2.53/1.05  
% 2.53/1.05  fof(f75,plain,(
% 2.53/1.05    m1_pre_topc(sK3,sK1)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f11,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f33,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f11])).
% 2.53/1.05  
% 2.53/1.05  fof(f34,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f33])).
% 2.53/1.05  
% 2.53/1.05  fof(f64,plain,(
% 2.53/1.05    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f34])).
% 2.53/1.05  
% 2.53/1.05  fof(f77,plain,(
% 2.53/1.05    m1_pre_topc(sK4,sK1)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f4,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f22,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f4])).
% 2.53/1.05  
% 2.53/1.05  fof(f55,plain,(
% 2.53/1.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f22])).
% 2.53/1.05  
% 2.53/1.05  fof(f70,plain,(
% 2.53/1.05    l1_pre_topc(sK1)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f2,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f18,plain,(
% 2.53/1.05    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f2])).
% 2.53/1.05  
% 2.53/1.05  fof(f19,plain,(
% 2.53/1.05    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(flattening,[],[f18])).
% 2.53/1.05  
% 2.53/1.05  fof(f53,plain,(
% 2.53/1.05    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f19])).
% 2.53/1.05  
% 2.53/1.05  fof(f74,plain,(
% 2.53/1.05    ~v2_struct_0(sK3)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f81,plain,(
% 2.53/1.05    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f6,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f24,plain,(
% 2.53/1.05    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f6])).
% 2.53/1.05  
% 2.53/1.05  fof(f25,plain,(
% 2.53/1.05    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f24])).
% 2.53/1.05  
% 2.53/1.05  fof(f58,plain,(
% 2.53/1.05    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f25])).
% 2.53/1.05  
% 2.53/1.05  fof(f7,axiom,(
% 2.53/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f26,plain,(
% 2.53/1.05    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.53/1.05    inference(ennf_transformation,[],[f7])).
% 2.53/1.05  
% 2.53/1.05  fof(f59,plain,(
% 2.53/1.05    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.53/1.05    inference(cnf_transformation,[],[f26])).
% 2.53/1.05  
% 2.53/1.05  fof(f5,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f23,plain,(
% 2.53/1.05    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f5])).
% 2.53/1.05  
% 2.53/1.05  fof(f56,plain,(
% 2.53/1.05    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f23])).
% 2.53/1.05  
% 2.53/1.05  fof(f68,plain,(
% 2.53/1.05    ~v2_struct_0(sK1)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f69,plain,(
% 2.53/1.05    v2_pre_topc(sK1)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f10,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f31,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f10])).
% 2.53/1.05  
% 2.53/1.05  fof(f32,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f31])).
% 2.53/1.05  
% 2.53/1.05  fof(f63,plain,(
% 2.53/1.05    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f32])).
% 2.53/1.05  
% 2.53/1.05  fof(f85,plain,(
% 2.53/1.05    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f84,plain,(
% 2.53/1.05    sK6 = sK7),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f9,axiom,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f29,plain,(
% 2.53/1.05    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f9])).
% 2.53/1.05  
% 2.53/1.05  fof(f30,plain,(
% 2.53/1.05    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f29])).
% 2.53/1.05  
% 2.53/1.05  fof(f41,plain,(
% 2.53/1.05    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f42,plain,(
% 2.53/1.05    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f41])).
% 2.53/1.05  
% 2.53/1.05  fof(f62,plain,(
% 2.53/1.05    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f42])).
% 2.53/1.05  
% 2.53/1.05  fof(f1,axiom,(
% 2.53/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f16,plain,(
% 2.53/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.53/1.05    inference(unused_predicate_definition_removal,[],[f1])).
% 2.53/1.05  
% 2.53/1.05  fof(f17,plain,(
% 2.53/1.05    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.53/1.05    inference(ennf_transformation,[],[f16])).
% 2.53/1.05  
% 2.53/1.05  fof(f52,plain,(
% 2.53/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.53/1.05    inference(cnf_transformation,[],[f17])).
% 2.53/1.05  
% 2.53/1.05  fof(f13,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f37,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f13])).
% 2.53/1.05  
% 2.53/1.05  fof(f38,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f37])).
% 2.53/1.05  
% 2.53/1.05  fof(f43,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(nnf_transformation,[],[f38])).
% 2.53/1.05  
% 2.53/1.05  fof(f67,plain,(
% 2.53/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f43])).
% 2.53/1.05  
% 2.53/1.05  fof(f87,plain,(
% 2.53/1.05    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(equality_resolution,[],[f67])).
% 2.53/1.05  
% 2.53/1.05  fof(f79,plain,(
% 2.53/1.05    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f78,plain,(
% 2.53/1.05    v1_funct_1(sK5)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f12,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f35,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f12])).
% 2.53/1.05  
% 2.53/1.05  fof(f36,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.53/1.05    inference(flattening,[],[f35])).
% 2.53/1.05  
% 2.53/1.05  fof(f65,plain,(
% 2.53/1.05    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f36])).
% 2.53/1.05  
% 2.53/1.05  fof(f8,axiom,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f27,plain,(
% 2.53/1.05    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f8])).
% 2.53/1.05  
% 2.53/1.05  fof(f28,plain,(
% 2.53/1.05    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f27])).
% 2.53/1.05  
% 2.53/1.05  fof(f61,plain,(
% 2.53/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f28])).
% 2.53/1.05  
% 2.53/1.05  fof(f3,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.53/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f20,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f3])).
% 2.53/1.05  
% 2.53/1.05  fof(f21,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.53/1.05    inference(flattening,[],[f20])).
% 2.53/1.05  
% 2.53/1.05  fof(f54,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f21])).
% 2.53/1.05  
% 2.53/1.05  fof(f71,plain,(
% 2.53/1.05    ~v2_struct_0(sK2)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f72,plain,(
% 2.53/1.05    v2_pre_topc(sK2)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f73,plain,(
% 2.53/1.05    l1_pre_topc(sK2)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f76,plain,(
% 2.53/1.05    ~v2_struct_0(sK4)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f80,plain,(
% 2.53/1.05    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f82,plain,(
% 2.53/1.05    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f86,plain,(
% 2.53/1.05    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f83,plain,(
% 2.53/1.05    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.53/1.05    inference(cnf_transformation,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  cnf(c_27,negated_conjecture,
% 2.53/1.05      ( m1_pre_topc(sK3,sK1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f75]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1567,plain,
% 2.53/1.05      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_12,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1576,plain,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 2.53/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_pre_topc(X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3783,plain,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_tsep_1(sK1,sK3,sK3)
% 2.53/1.05      | v2_struct_0(sK1) = iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_1567,c_1576]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_25,negated_conjecture,
% 2.53/1.05      ( m1_pre_topc(sK4,sK1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1569,plain,
% 2.53/1.05      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1583,plain,
% 2.53/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2722,plain,
% 2.53/1.05      ( l1_pre_topc(sK1) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK4) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_1569,c_1583]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_32,negated_conjecture,
% 2.53/1.05      ( l1_pre_topc(sK1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_37,plain,
% 2.53/1.05      ( l1_pre_topc(sK1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2913,plain,
% 2.53/1.05      ( l1_pre_topc(sK4) = iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_2722,c_37]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1,plain,
% 2.53/1.05      ( ~ l1_pre_topc(X0)
% 2.53/1.05      | ~ v1_pre_topc(X0)
% 2.53/1.05      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.53/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1585,plain,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top
% 2.53/1.05      | v1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3088,plain,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
% 2.53/1.05      | v1_pre_topc(sK4) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_2913,c_1585]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_28,negated_conjecture,
% 2.53/1.05      ( ~ v2_struct_0(sK3) ),
% 2.53/1.05      inference(cnf_transformation,[],[f74]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_41,plain,
% 2.53/1.05      ( v2_struct_0(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2723,plain,
% 2.53/1.05      ( l1_pre_topc(sK1) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_1567,c_1583]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_21,negated_conjecture,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
% 2.53/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_5,plain,
% 2.53/1.05      ( v2_struct_0(X0)
% 2.53/1.05      | ~ l1_pre_topc(X0)
% 2.53/1.05      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.53/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1581,plain,
% 2.53/1.05      ( v2_struct_0(X0) = iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top
% 2.53/1.05      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2840,plain,
% 2.53/1.05      ( v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top
% 2.53/1.05      | v1_pre_topc(sK4) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_21,c_1581]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3436,plain,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_3088,c_37,c_41,c_2723,c_2840]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_8,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.53/1.05      | X2 = X1
% 2.53/1.05      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1578,plain,
% 2.53/1.05      ( X0 = X1
% 2.53/1.05      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.53/1.05      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3251,plain,
% 2.53/1.05      ( g1_pre_topc(X0,X1) != sK4
% 2.53/1.05      | u1_struct_0(sK3) = X0
% 2.53/1.05      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_21,c_1578]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4,plain,
% 2.53/1.05      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.53/1.05      | ~ l1_pre_topc(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3001,plain,
% 2.53/1.05      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 2.53/1.05      | ~ l1_pre_topc(sK3) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_4]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3006,plain,
% 2.53/1.05      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_3001]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3252,plain,
% 2.53/1.05      ( g1_pre_topc(X0,X1) != sK4
% 2.53/1.05      | u1_struct_0(sK3) = X0
% 2.53/1.05      | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_21,c_1578]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3309,plain,
% 2.53/1.05      ( u1_struct_0(sK3) = X0 | g1_pre_topc(X0,X1) != sK4 ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_3251,c_37,c_2723,c_3006,c_3252]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3310,plain,
% 2.53/1.05      ( g1_pre_topc(X0,X1) != sK4 | u1_struct_0(sK3) = X0 ),
% 2.53/1.05      inference(renaming,[status(thm)],[c_3309]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3441,plain,
% 2.53/1.05      ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3436,c_3310]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3528,plain,
% 2.53/1.05      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK3)) = sK4 ),
% 2.53/1.05      inference(demodulation,[status(thm)],[c_3441,c_21]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3789,plain,
% 2.53/1.05      ( k1_tsep_1(sK1,sK3,sK3) = sK4
% 2.53/1.05      | v2_struct_0(sK1) = iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.53/1.05      inference(light_normalisation,[status(thm)],[c_3783,c_3441,c_3528]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_34,negated_conjecture,
% 2.53/1.05      ( ~ v2_struct_0(sK1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_35,plain,
% 2.53/1.05      ( v2_struct_0(sK1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_33,negated_conjecture,
% 2.53/1.05      ( v2_pre_topc(sK1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_36,plain,
% 2.53/1.05      ( v2_pre_topc(sK1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4310,plain,
% 2.53/1.05      ( k1_tsep_1(sK1,sK3,sK3) = sK4 ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_3789,c_35,c_36,c_37,c_41]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_11,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | ~ m1_pre_topc(X2,X1)
% 2.53/1.05      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f63]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1577,plain,
% 2.53/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.53/1.05      | m1_pre_topc(X2,X1) != iProver_top
% 2.53/1.05      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(X2) = iProver_top
% 2.53/1.05      | v2_pre_topc(X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4313,plain,
% 2.53/1.05      ( m1_pre_topc(sK3,sK1) != iProver_top
% 2.53/1.05      | m1_pre_topc(sK3,sK4) = iProver_top
% 2.53/1.05      | v2_struct_0(sK1) = iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_4310,c_1577]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_17,negated_conjecture,
% 2.53/1.05      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.53/1.05      inference(cnf_transformation,[],[f85]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1573,plain,
% 2.53/1.05      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_18,negated_conjecture,
% 2.53/1.05      ( sK6 = sK7 ),
% 2.53/1.05      inference(cnf_transformation,[],[f84]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1619,plain,
% 2.53/1.05      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
% 2.53/1.05      inference(light_normalisation,[status(thm)],[c_1573,c_18]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_10,plain,
% 2.53/1.05      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.53/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v2_pre_topc(X0)
% 2.53/1.05      | ~ l1_pre_topc(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_0,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_14,plain,
% 2.53/1.05      ( r1_tmap_1(X0,X1,X2,X3)
% 2.53/1.05      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.53/1.05      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.53/1.05      | ~ m1_connsp_2(X6,X0,X3)
% 2.53/1.05      | ~ m1_pre_topc(X4,X5)
% 2.53/1.05      | ~ m1_pre_topc(X0,X5)
% 2.53/1.05      | ~ m1_pre_topc(X4,X0)
% 2.53/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.53/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.53/1.05      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.53/1.05      | ~ v1_funct_1(X2)
% 2.53/1.05      | v2_struct_0(X5)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X4)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v2_pre_topc(X5)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X5)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_23,negated_conjecture,
% 2.53/1.05      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.53/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_442,plain,
% 2.53/1.05      ( r1_tmap_1(X0,X1,X2,X3)
% 2.53/1.05      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.53/1.05      | ~ m1_connsp_2(X6,X0,X3)
% 2.53/1.05      | ~ m1_pre_topc(X4,X5)
% 2.53/1.05      | ~ m1_pre_topc(X0,X5)
% 2.53/1.05      | ~ m1_pre_topc(X4,X0)
% 2.53/1.05      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.53/1.05      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.53/1.05      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.53/1.05      | ~ v1_funct_1(X2)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X5)
% 2.53/1.05      | v2_struct_0(X4)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X5)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X5)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.53/1.05      | sK5 != X2 ),
% 2.53/1.05      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_443,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 2.53/1.05      | ~ m1_pre_topc(X0,X2)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.53/1.05      | ~ v1_funct_1(sK5)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(unflattening,[status(thm)],[c_442]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_24,negated_conjecture,
% 2.53/1.05      ( v1_funct_1(sK5) ),
% 2.53/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_447,plain,
% 2.53/1.05      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X2)
% 2.53/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_443,c_24]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_448,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(renaming,[status(thm)],[c_447]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_13,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | ~ m1_pre_topc(X2,X0)
% 2.53/1.05      | m1_pre_topc(X2,X1)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_495,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(forward_subsumption_resolution,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_448,c_13]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_519,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | X5 != X6
% 2.53/1.05      | u1_struct_0(X0) != X7
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_495]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_520,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_connsp_2(X5,X3,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(unflattening,[status(thm)],[c_519]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_741,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | v2_struct_0(X6)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X6)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X6)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | X3 != X6
% 2.53/1.05      | X4 != X5
% 2.53/1.05      | sK0(X6,X5) != X7
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_520]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_742,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
% 2.53/1.05      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ v2_pre_topc(X3)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X3)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(unflattening,[status(thm)],[c_741]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_9,plain,
% 2.53/1.05      ( ~ m1_connsp_2(X0,X1,X2)
% 2.53/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.53/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f61]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_653,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.05      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.53/1.05      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X3)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X3)
% 2.53/1.05      | X3 != X1
% 2.53/1.05      | X2 != X0
% 2.53/1.05      | sK0(X3,X2) != X4 ),
% 2.53/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_654,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.05      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(unflattening,[status(thm)],[c_653]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_767,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ v2_pre_topc(X3)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X3)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(forward_subsumption_resolution,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_742,c_654]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | v2_pre_topc(X0)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f54]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_788,plain,
% 2.53/1.05      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.53/1.05      | r1_tmap_1(X3,X1,sK5,X4)
% 2.53/1.05      | ~ m1_pre_topc(X3,X2)
% 2.53/1.05      | ~ m1_pre_topc(X0,X3)
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.53/1.05      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X3)
% 2.53/1.05      | v2_struct_0(X2)
% 2.53/1.05      | ~ v2_pre_topc(X1)
% 2.53/1.05      | ~ v2_pre_topc(X2)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | ~ l1_pre_topc(X2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.53/1.05      inference(forward_subsumption_resolution,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_767,c_3,c_2]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1557,plain,
% 2.53/1.05      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.53/1.05      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.53/1.05      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
% 2.53/1.05      | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X3) != iProver_top
% 2.53/1.05      | m1_pre_topc(X2,X1) != iProver_top
% 2.53/1.05      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.53/1.05      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(X1,X4),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 2.53/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(X2) = iProver_top
% 2.53/1.05      | v2_struct_0(X3) = iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_pre_topc(X0) != iProver_top
% 2.53/1.05      | v2_pre_topc(X3) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2000,plain,
% 2.53/1.05      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.53/1.05      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.53/1.05      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.53/1.05      | m1_pre_topc(X0,X2) != iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.53/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(X2) = iProver_top
% 2.53/1.05      | v2_struct_0(sK2) = iProver_top
% 2.53/1.05      | v2_pre_topc(X2) != iProver_top
% 2.53/1.05      | v2_pre_topc(sK2) != iProver_top
% 2.53/1.05      | l1_pre_topc(X2) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK2) != iProver_top ),
% 2.53/1.05      inference(equality_resolution,[status(thm)],[c_1557]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_31,negated_conjecture,
% 2.53/1.05      ( ~ v2_struct_0(sK2) ),
% 2.53/1.05      inference(cnf_transformation,[],[f71]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_38,plain,
% 2.53/1.05      ( v2_struct_0(sK2) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_30,negated_conjecture,
% 2.53/1.05      ( v2_pre_topc(sK2) ),
% 2.53/1.05      inference(cnf_transformation,[],[f72]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_39,plain,
% 2.53/1.05      ( v2_pre_topc(sK2) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_29,negated_conjecture,
% 2.53/1.05      ( l1_pre_topc(sK2) ),
% 2.53/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_40,plain,
% 2.53/1.05      ( l1_pre_topc(sK2) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2481,plain,
% 2.53/1.05      ( l1_pre_topc(X2) != iProver_top
% 2.53/1.05      | v2_struct_0(X2) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.53/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.53/1.05      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | m1_pre_topc(X0,X2) != iProver_top
% 2.53/1.05      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.53/1.05      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.53/1.05      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.53/1.05      | v2_pre_topc(X2) != iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_2000,c_38,c_39,c_40]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2482,plain,
% 2.53/1.05      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.53/1.05      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.53/1.05      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.53/1.05      | m1_pre_topc(X0,X2) != iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.53/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(X2) = iProver_top
% 2.53/1.05      | v2_pre_topc(X2) != iProver_top
% 2.53/1.05      | l1_pre_topc(X2) != iProver_top ),
% 2.53/1.05      inference(renaming,[status(thm)],[c_2481]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2499,plain,
% 2.53/1.05      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.53/1.05      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.53/1.05      | m1_pre_topc(X0,sK4) != iProver_top
% 2.53/1.05      | m1_pre_topc(sK4,X1) != iProver_top
% 2.53/1.05      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.53/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(sK4) = iProver_top
% 2.53/1.05      | v2_pre_topc(X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(equality_resolution,[status(thm)],[c_2482]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_26,negated_conjecture,
% 2.53/1.05      ( ~ v2_struct_0(sK4) ),
% 2.53/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_43,plain,
% 2.53/1.05      ( v2_struct_0(sK4) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_22,negated_conjecture,
% 2.53/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.53/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_47,plain,
% 2.53/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3009,plain,
% 2.53/1.05      ( v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.53/1.05      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.53/1.05      | m1_pre_topc(X0,sK4) != iProver_top
% 2.53/1.05      | m1_pre_topc(sK4,X1) != iProver_top
% 2.53/1.05      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.53/1.05      | v2_pre_topc(X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_2499,c_43,c_47]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3010,plain,
% 2.53/1.05      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.53/1.05      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.53/1.05      | m1_pre_topc(X0,sK4) != iProver_top
% 2.53/1.05      | m1_pre_topc(sK4,X1) != iProver_top
% 2.53/1.05      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(sK4,X2),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v2_pre_topc(X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(renaming,[status(thm)],[c_3009]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3026,plain,
% 2.53/1.05      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.53/1.05      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.53/1.05      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.53/1.05      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK1) = iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_1619,c_3010]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_44,plain,
% 2.53/1.05      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_20,negated_conjecture,
% 2.53/1.05      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.53/1.05      inference(cnf_transformation,[],[f82]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_48,plain,
% 2.53/1.05      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_16,negated_conjecture,
% 2.53/1.05      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
% 2.53/1.05      inference(cnf_transformation,[],[f86]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_51,plain,
% 2.53/1.05      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_19,negated_conjecture,
% 2.53/1.05      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.53/1.05      inference(cnf_transformation,[],[f83]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1572,plain,
% 2.53/1.05      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1610,plain,
% 2.53/1.05      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(light_normalisation,[status(thm)],[c_1572,c_18]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3029,plain,
% 2.53/1.05      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_3026,c_35,c_36,c_37,c_41,c_44,c_48,c_51,c_1610]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3526,plain,
% 2.53/1.05      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.53/1.05      | m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.53/1.05      inference(demodulation,[status(thm)],[c_3441,c_3029]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2315,plain,
% 2.53/1.05      ( ~ m1_pre_topc(sK4,X0)
% 2.53/1.05      | ~ v2_pre_topc(X0)
% 2.53/1.05      | v2_pre_topc(sK4)
% 2.53/1.05      | ~ l1_pre_topc(X0) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2924,plain,
% 2.53/1.05      ( ~ m1_pre_topc(sK4,sK1)
% 2.53/1.05      | ~ v2_pre_topc(sK1)
% 2.53/1.05      | v2_pre_topc(sK4)
% 2.53/1.05      | ~ l1_pre_topc(sK1) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_2315]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2925,plain,
% 2.53/1.05      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.53/1.05      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.05      | v2_pre_topc(sK4) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1913,plain,
% 2.53/1.05      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.53/1.05      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.53/1.05      | v2_struct_0(sK4)
% 2.53/1.05      | ~ v2_pre_topc(sK4)
% 2.53/1.05      | ~ l1_pre_topc(sK4) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_654]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1914,plain,
% 2.53/1.05      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.53/1.05      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK4) = iProver_top
% 2.53/1.05      | v2_pre_topc(sK4) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK4) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_42,plain,
% 2.53/1.05      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(contradiction,plain,
% 2.53/1.05      ( $false ),
% 2.53/1.05      inference(minisat,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_4313,c_3526,c_2925,c_2722,c_1914,c_48,c_44,c_43,c_42,
% 2.53/1.05                 c_41,c_37,c_36,c_35]) ).
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  ------                               Statistics
% 2.53/1.05  
% 2.53/1.05  ------ General
% 2.53/1.05  
% 2.53/1.05  abstr_ref_over_cycles:                  0
% 2.53/1.05  abstr_ref_under_cycles:                 0
% 2.53/1.05  gc_basic_clause_elim:                   0
% 2.53/1.05  forced_gc_time:                         0
% 2.53/1.05  parsing_time:                           0.013
% 2.53/1.05  unif_index_cands_time:                  0.
% 2.53/1.05  unif_index_add_time:                    0.
% 2.53/1.05  orderings_time:                         0.
% 2.53/1.05  out_proof_time:                         0.029
% 2.53/1.05  total_time:                             0.246
% 2.53/1.05  num_of_symbols:                         57
% 2.53/1.05  num_of_terms:                           3999
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing
% 2.53/1.05  
% 2.53/1.05  num_of_splits:                          0
% 2.53/1.05  num_of_split_atoms:                     0
% 2.53/1.05  num_of_reused_defs:                     0
% 2.53/1.05  num_eq_ax_congr_red:                    18
% 2.53/1.05  num_of_sem_filtered_clauses:            1
% 2.53/1.05  num_of_subtypes:                        0
% 2.53/1.05  monotx_restored_types:                  0
% 2.53/1.05  sat_num_of_epr_types:                   0
% 2.53/1.05  sat_num_of_non_cyclic_types:            0
% 2.53/1.05  sat_guarded_non_collapsed_types:        0
% 2.53/1.05  num_pure_diseq_elim:                    0
% 2.53/1.05  simp_replaced_by:                       0
% 2.53/1.05  res_preprocessed:                       159
% 2.53/1.05  prep_upred:                             0
% 2.53/1.05  prep_unflattend:                        17
% 2.53/1.05  smt_new_axioms:                         0
% 2.53/1.05  pred_elim_cands:                        7
% 2.53/1.05  pred_elim:                              4
% 2.53/1.05  pred_elim_cl:                           4
% 2.53/1.05  pred_elim_cycles:                       7
% 2.53/1.05  merged_defs:                            0
% 2.53/1.05  merged_defs_ncl:                        0
% 2.53/1.05  bin_hyper_res:                          0
% 2.53/1.05  prep_cycles:                            4
% 2.53/1.05  pred_elim_time:                         0.029
% 2.53/1.05  splitting_time:                         0.
% 2.53/1.05  sem_filter_time:                        0.
% 2.53/1.05  monotx_time:                            0.001
% 2.53/1.05  subtype_inf_time:                       0.
% 2.53/1.05  
% 2.53/1.05  ------ Problem properties
% 2.53/1.05  
% 2.53/1.05  clauses:                                31
% 2.53/1.05  conjectures:                            17
% 2.53/1.05  epr:                                    15
% 2.53/1.05  horn:                                   25
% 2.53/1.05  ground:                                 17
% 2.53/1.05  unary:                                  17
% 2.53/1.05  binary:                                 1
% 2.53/1.05  lits:                                   101
% 2.53/1.05  lits_eq:                                12
% 2.53/1.05  fd_pure:                                0
% 2.53/1.05  fd_pseudo:                              0
% 2.53/1.05  fd_cond:                                0
% 2.53/1.05  fd_pseudo_cond:                         2
% 2.53/1.05  ac_symbols:                             0
% 2.53/1.05  
% 2.53/1.05  ------ Propositional Solver
% 2.53/1.05  
% 2.53/1.05  prop_solver_calls:                      26
% 2.53/1.05  prop_fast_solver_calls:                 1500
% 2.53/1.05  smt_solver_calls:                       0
% 2.53/1.05  smt_fast_solver_calls:                  0
% 2.53/1.05  prop_num_of_clauses:                    1335
% 2.53/1.05  prop_preprocess_simplified:             4828
% 2.53/1.05  prop_fo_subsumed:                       40
% 2.53/1.05  prop_solver_time:                       0.
% 2.53/1.05  smt_solver_time:                        0.
% 2.53/1.05  smt_fast_solver_time:                   0.
% 2.53/1.05  prop_fast_solver_time:                  0.
% 2.53/1.05  prop_unsat_core_time:                   0.
% 2.53/1.05  
% 2.53/1.05  ------ QBF
% 2.53/1.05  
% 2.53/1.05  qbf_q_res:                              0
% 2.53/1.05  qbf_num_tautologies:                    0
% 2.53/1.05  qbf_prep_cycles:                        0
% 2.53/1.05  
% 2.53/1.05  ------ BMC1
% 2.53/1.05  
% 2.53/1.05  bmc1_current_bound:                     -1
% 2.53/1.05  bmc1_last_solved_bound:                 -1
% 2.53/1.05  bmc1_unsat_core_size:                   -1
% 2.53/1.05  bmc1_unsat_core_parents_size:           -1
% 2.53/1.05  bmc1_merge_next_fun:                    0
% 2.53/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.05  
% 2.53/1.05  ------ Instantiation
% 2.53/1.05  
% 2.53/1.05  inst_num_of_clauses:                    380
% 2.53/1.05  inst_num_in_passive:                    48
% 2.53/1.05  inst_num_in_active:                     246
% 2.53/1.05  inst_num_in_unprocessed:                86
% 2.53/1.05  inst_num_of_loops:                      270
% 2.53/1.05  inst_num_of_learning_restarts:          0
% 2.53/1.05  inst_num_moves_active_passive:          21
% 2.53/1.05  inst_lit_activity:                      0
% 2.53/1.05  inst_lit_activity_moves:                0
% 2.53/1.05  inst_num_tautologies:                   0
% 2.53/1.05  inst_num_prop_implied:                  0
% 2.53/1.05  inst_num_existing_simplified:           0
% 2.53/1.05  inst_num_eq_res_simplified:             0
% 2.53/1.05  inst_num_child_elim:                    0
% 2.53/1.05  inst_num_of_dismatching_blockings:      32
% 2.53/1.05  inst_num_of_non_proper_insts:           448
% 2.53/1.05  inst_num_of_duplicates:                 0
% 2.53/1.05  inst_inst_num_from_inst_to_res:         0
% 2.53/1.05  inst_dismatching_checking_time:         0.
% 2.53/1.05  
% 2.53/1.05  ------ Resolution
% 2.53/1.05  
% 2.53/1.05  res_num_of_clauses:                     0
% 2.53/1.05  res_num_in_passive:                     0
% 2.53/1.05  res_num_in_active:                      0
% 2.53/1.05  res_num_of_loops:                       163
% 2.53/1.05  res_forward_subset_subsumed:            36
% 2.53/1.05  res_backward_subset_subsumed:           0
% 2.53/1.05  res_forward_subsumed:                   0
% 2.53/1.05  res_backward_subsumed:                  0
% 2.53/1.05  res_forward_subsumption_resolution:     8
% 2.53/1.05  res_backward_subsumption_resolution:    0
% 2.53/1.05  res_clause_to_clause_subsumption:       226
% 2.53/1.05  res_orphan_elimination:                 0
% 2.53/1.05  res_tautology_del:                      43
% 2.53/1.05  res_num_eq_res_simplified:              0
% 2.53/1.05  res_num_sel_changes:                    0
% 2.53/1.05  res_moves_from_active_to_pass:          0
% 2.53/1.05  
% 2.53/1.05  ------ Superposition
% 2.53/1.05  
% 2.53/1.05  sup_time_total:                         0.
% 2.53/1.05  sup_time_generating:                    0.
% 2.53/1.05  sup_time_sim_full:                      0.
% 2.53/1.05  sup_time_sim_immed:                     0.
% 2.53/1.05  
% 2.53/1.05  sup_num_of_clauses:                     66
% 2.53/1.05  sup_num_in_active:                      49
% 2.53/1.05  sup_num_in_passive:                     17
% 2.53/1.05  sup_num_of_loops:                       53
% 2.53/1.05  sup_fw_superposition:                   26
% 2.53/1.05  sup_bw_superposition:                   21
% 2.53/1.05  sup_immediate_simplified:               13
% 2.53/1.05  sup_given_eliminated:                   1
% 2.53/1.05  comparisons_done:                       0
% 2.53/1.05  comparisons_avoided:                    0
% 2.53/1.05  
% 2.53/1.05  ------ Simplifications
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  sim_fw_subset_subsumed:                 3
% 2.53/1.05  sim_bw_subset_subsumed:                 6
% 2.53/1.05  sim_fw_subsumed:                        2
% 2.53/1.05  sim_bw_subsumed:                        0
% 2.53/1.05  sim_fw_subsumption_res:                 0
% 2.53/1.05  sim_bw_subsumption_res:                 0
% 2.53/1.05  sim_tautology_del:                      2
% 2.53/1.05  sim_eq_tautology_del:                   5
% 2.53/1.05  sim_eq_res_simp:                        0
% 2.53/1.05  sim_fw_demodulated:                     0
% 2.53/1.05  sim_bw_demodulated:                     5
% 2.53/1.05  sim_light_normalised:                   10
% 2.53/1.05  sim_joinable_taut:                      0
% 2.53/1.05  sim_joinable_simp:                      0
% 2.53/1.05  sim_ac_normalised:                      0
% 2.53/1.05  sim_smt_subsumption:                    0
% 2.53/1.05  
%------------------------------------------------------------------------------
