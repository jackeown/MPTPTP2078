%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:17 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  210 (3351 expanded)
%              Number of clauses        :  148 ( 579 expanded)
%              Number of leaves         :   14 (1534 expanded)
%              Depth                    :   29
%              Number of atoms          : 1883 (73658 expanded)
%              Number of equality atoms :  671 (12040 expanded)
%              Maximal formula depth    :   30 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( ( X5 = X7
                                        & X5 = X6 )
                                     => ( r1_tmap_1(X0,X1,X2,X5)
                                      <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X4))
                                     => ( ( X5 = X7
                                          & X5 = X6 )
                                       => ( r1_tmap_1(X0,X1,X2,X5)
                                        <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
            | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
            | ~ r1_tmap_1(X0,X1,X2,X5) )
          & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
            | r1_tmap_1(X0,X1,X2,X5) )
          & X5 = X7
          & X5 = X6
          & m1_subset_1(X7,u1_struct_0(X4)) )
     => ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
          | ~ r1_tmap_1(X0,X1,X2,X5) )
        & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7)
            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
          | r1_tmap_1(X0,X1,X2,X5) )
        & sK7 = X5
        & X5 = X6
        & m1_subset_1(sK7,u1_struct_0(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                | ~ r1_tmap_1(X0,X1,X2,X5) )
              & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                | r1_tmap_1(X0,X1,X2,X5) )
              & X5 = X7
              & X5 = X6
              & m1_subset_1(X7,u1_struct_0(X4)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
              | ~ r1_tmap_1(X0,X1,X2,X5) )
            & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) )
              | r1_tmap_1(X0,X1,X2,X5) )
            & X5 = X7
            & sK6 = X5
            & m1_subset_1(X7,u1_struct_0(X4)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                    | r1_tmap_1(X0,X1,X2,X5) )
                  & X5 = X7
                  & X5 = X6
                  & m1_subset_1(X7,u1_struct_0(X4)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                  | ~ r1_tmap_1(X0,X1,X2,sK5) )
                & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                    & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                  | r1_tmap_1(X0,X1,X2,sK5) )
                & sK5 = X7
                & sK5 = X6
                & m1_subset_1(X7,u1_struct_0(X4)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                        | ~ r1_tmap_1(X0,X1,X2,X5) )
                      & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                        | r1_tmap_1(X0,X1,X2,X5) )
                      & X5 = X7
                      & X5 = X6
                      & m1_subset_1(X7,u1_struct_0(X4)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & k1_tsep_1(X0,X3,X4) = X0
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                    & ( ( r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7)
                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                      | r1_tmap_1(X0,X1,X2,X5) )
                    & X5 = X7
                    & X5 = X6
                    & m1_subset_1(X7,u1_struct_0(sK4)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & k1_tsep_1(X0,X3,sK4) = X0
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                            | ~ r1_tmap_1(X0,X1,X2,X5) )
                          & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                            | r1_tmap_1(X0,X1,X2,X5) )
                          & X5 = X7
                          & X5 = X6
                          & m1_subset_1(X7,u1_struct_0(X4)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & k1_tsep_1(X0,X3,X4) = X0
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)
                          | ~ r1_tmap_1(X0,X1,X2,X5) )
                        & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                            & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) )
                          | r1_tmap_1(X0,X1,X2,X5) )
                        & X5 = X7
                        & X5 = X6
                        & m1_subset_1(X7,u1_struct_0(X4)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & k1_tsep_1(X0,sK3,X4) = X0
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                | ~ r1_tmap_1(X0,X1,X2,X5) )
                              & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                | r1_tmap_1(X0,X1,X2,X5) )
                              & X5 = X7
                              & X5 = X6
                              & m1_subset_1(X7,u1_struct_0(X4)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & k1_tsep_1(X0,X3,X4) = X0
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)
                              | ~ r1_tmap_1(X0,X1,sK2,X5) )
                            & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) )
                              | r1_tmap_1(X0,X1,sK2,X5) )
                            & X5 = X7
                            & X5 = X6
                            & m1_subset_1(X7,u1_struct_0(X4)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & k1_tsep_1(X0,X3,X4) = X0
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)
                                  | ~ r1_tmap_1(X0,sK1,X2,X5) )
                                & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7)
                                    & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) )
                                  | r1_tmap_1(X0,sK1,X2,X5) )
                                & X5 = X7
                                & X5 = X6
                                & m1_subset_1(X7,u1_struct_0(X4)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & k1_tsep_1(X0,X3,X4) = X0
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | r1_tmap_1(X0,X1,X2,X5) )
                                    & X5 = X7
                                    & X5 = X6
                                    & m1_subset_1(X7,u1_struct_0(X4)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(sK0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) )
                                    | r1_tmap_1(sK0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & k1_tsep_1(sK0,X3,X4) = sK0
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
      | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
    & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
      | r1_tmap_1(sK0,sK1,sK2,sK5) )
    & sK5 = sK7
    & sK5 = sK6
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & k1_tsep_1(sK0,sK3,sK4) = sK0
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f27,f26,f25,f24,f23,f22,f21,f20])).

fof(f54,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
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
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(flattening,[],[f9])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
                                 => ( ( X6 = X7
                                      & X5 = X7 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                    <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                  <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                  <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f11])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                    & ( ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                    & ( ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | X6 != X7
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f33])).

fof(f58,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f57])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X6 != X7
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f31])).

fof(f62,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f61])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X6 != X7
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | X5 != X7
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f32])).

fof(f60,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f59])).

fof(f56,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_736,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1196,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_9,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_735,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_10,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_734,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1218,plain,
    ( sK6 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_734,c_735])).

cnf(c_1262,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1196,c_735,c_1218])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_729,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1200,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_260,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_264,plain,
    ( ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_21])).

cnf(c_265,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_718,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK2) ),
    inference(subtyping,[status(esa)],[c_265])).

cnf(c_1211,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1952,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1211])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_32,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_33,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_743,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1489,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1493,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X1_51,sK1,X0_51,X2_51,sK2) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1499,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_2541,plain,
    ( l1_pre_topc(X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1952,c_31,c_32,c_33,c_1489,c_1499])).

cnf(c_2542,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2541])).

cnf(c_2556,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2542])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2689,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2556,c_36])).

cnf(c_2702,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_2689])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_315,plain,
    ( ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_21])).

cnf(c_316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_717,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X2_51,X0_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_1212,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_2047,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1212])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X1_51,X0_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1495,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_2561,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2047,c_31,c_32,c_33,c_1489,c_1495])).

cnf(c_2562,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2561])).

cnf(c_2574,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2562])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_28,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_29,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2642,plain,
    ( m1_pre_topc(X0_51,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_28,c_29,c_30,c_36])).

cnf(c_2643,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
    | m1_pre_topc(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2642])).

cnf(c_2650,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1200,c_2643])).

cnf(c_2736,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2702,c_2650])).

cnf(c_40,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_47,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_49,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_2963,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2736,c_28,c_29,c_30,c_40,c_49])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_727,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1202,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_2703,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_2689])).

cnf(c_2651,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1202,c_2643])).

cnf(c_2723,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2703,c_2651])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2829,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2723,c_28,c_29,c_30,c_38,c_49])).

cnf(c_14,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_730,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X5)
    | r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_421,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X5)
    | r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0)
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_422,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
    | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_21])).

cnf(c_427,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
    | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_426])).

cnf(c_715,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X0_51,sK2),X0_52)
    | ~ r1_tmap_1(X3_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X3_51,sK2),X0_52)
    | r1_tmap_1(k1_tsep_1(X2_51,X0_51,X3_51),X1_51,sK2,X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_1214,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
    | r1_tmap_1(X2_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X2_51,sK2),X0_52) != iProver_top
    | r1_tmap_1(X3_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X3_51,sK2),X0_52) != iProver_top
    | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(X3_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_2352,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK3,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_1214])).

cnf(c_2353,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2352,c_730])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_39,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2424,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
    | u1_struct_0(X0_51) != u1_struct_0(sK1)
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2353,c_28,c_29,c_30,c_37,c_38,c_39,c_40])).

cnf(c_2425,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2424])).

cnf(c_2441,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2425])).

cnf(c_2446,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2441,c_31,c_32,c_33,c_36])).

cnf(c_2832,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2829,c_2446])).

cnf(c_2966,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2963,c_2832])).

cnf(c_3333,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_2966])).

cnf(c_4,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,X4),X5)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_490,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,X4),X5)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,X4,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0)
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_491,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_493,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_21])).

cnf(c_494,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_714,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X0_51,sK2),X0_52)
    | ~ r1_tmap_1(k1_tsep_1(X2_51,X0_51,X3_51),X1_51,sK2,X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1215,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
    | r1_tmap_1(X2_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X2_51,sK2),X0_52) = iProver_top
    | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(X3_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2218,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK3,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_1215])).

cnf(c_2219,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2218,c_730])).

cnf(c_2224,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
    | u1_struct_0(X0_51) != u1_struct_0(sK1)
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_28,c_29,c_30,c_37,c_38,c_39,c_40])).

cnf(c_2225,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2224])).

cnf(c_2240,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2225])).

cnf(c_2321,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2240,c_31,c_32,c_33,c_36])).

cnf(c_2833,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2829,c_2321])).

cnf(c_3,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_355,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0)
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_356,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_21])).

cnf(c_361,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_716,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X3_51,X0_51),X0_51,sK2),X0_52)
    | ~ r1_tmap_1(k1_tsep_1(X2_51,X3_51,X0_51),X1_51,sK2,X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_1213,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
    | r1_tmap_1(X3_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X3_51,sK2),X0_52) = iProver_top
    | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | m1_pre_topc(X3_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2070,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_1213])).

cnf(c_2071,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2070,c_730])).

cnf(c_2125,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
    | u1_struct_0(X0_51) != u1_struct_0(sK1)
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2071,c_28,c_29,c_30,c_37,c_38,c_39,c_40])).

cnf(c_2126,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK1)
    | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2125])).

cnf(c_2141,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2126])).

cnf(c_2146,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2141,c_31,c_32,c_33,c_36])).

cnf(c_2967,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2963,c_2146])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_738,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1194,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_1267,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1194,c_735,c_1218])).

cnf(c_3053,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2967,c_1267])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_731,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1199,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_1246,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1199,c_735])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_732,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1198,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_1243,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1198,c_1218])).

cnf(c_3056,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_43,c_1246,c_1243])).

cnf(c_3057,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_3056])).

cnf(c_3063,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_3057])).

cnf(c_7,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_737,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1195,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1257,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1195,c_735])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3333,c_3063,c_1257,c_1243,c_1246,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:02:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.17/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.98  
% 2.17/0.98  ------  iProver source info
% 2.17/0.98  
% 2.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.98  git: non_committed_changes: false
% 2.17/0.98  git: last_make_outside_of_git: false
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     num_symb
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       true
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  ------ Parsing...
% 2.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.98  ------ Proving...
% 2.17/0.98  ------ Problem Properties 
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  clauses                                 26
% 2.17/0.98  conjectures                             20
% 2.17/0.98  EPR                                     13
% 2.17/0.98  Horn                                    19
% 2.17/0.98  unary                                   17
% 2.17/0.98  binary                                  3
% 2.17/0.98  lits                                    105
% 2.17/0.98  lits eq                                 15
% 2.17/0.98  fd_pure                                 0
% 2.17/0.98  fd_pseudo                               0
% 2.17/0.98  fd_cond                                 0
% 2.17/0.98  fd_pseudo_cond                          0
% 2.17/0.98  AC symbols                              0
% 2.17/0.98  
% 2.17/0.98  ------ Schedule dynamic 5 is on 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  Current options:
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     none
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       false
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ Proving...
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS status Theorem for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  fof(f5,conjecture,(
% 2.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f6,negated_conjecture,(
% 2.17/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.17/0.98    inference(negated_conjecture,[],[f5])).
% 2.17/0.98  
% 2.17/0.98  fof(f14,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f6])).
% 2.17/0.98  
% 2.17/0.98  fof(f15,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.98    inference(flattening,[],[f14])).
% 2.17/0.98  
% 2.17/0.98  fof(f18,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.98    inference(nnf_transformation,[],[f15])).
% 2.17/0.98  
% 2.17/0.98  fof(f19,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.17/0.98    inference(flattening,[],[f18])).
% 2.17/0.98  
% 2.17/0.98  fof(f27,plain,(
% 2.17/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK7 = X5 & X5 = X6 & m1_subset_1(sK7,u1_struct_0(X4)))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f26,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK6 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f25,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f24,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK4) = X0 & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f23,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f22,plain,(
% 2.17/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) | ~r1_tmap_1(X0,X1,sK2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)) | r1_tmap_1(X0,X1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f21,plain,(
% 2.17/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) | ~r1_tmap_1(X0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)) | r1_tmap_1(X0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f20,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & k1_tsep_1(sK0,X3,X4) = sK0 & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f28,plain,(
% 2.17/0.98    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & k1_tsep_1(sK0,sK3,sK4) = sK0 & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f19,f27,f26,f25,f24,f23,f22,f21,f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f54,plain,(
% 2.17/0.98    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f53,plain,(
% 2.17/0.98    sK5 = sK7),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f52,plain,(
% 2.17/0.98    sK5 = sK6),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f47,plain,(
% 2.17/0.98    m1_pre_topc(sK4,sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f2,axiom,(
% 2.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f9,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f2])).
% 2.17/0.98  
% 2.17/0.98  fof(f10,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.98    inference(flattening,[],[f9])).
% 2.17/0.98  
% 2.17/0.98  fof(f30,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f10])).
% 2.17/0.98  
% 2.17/0.98  fof(f42,plain,(
% 2.17/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f41,plain,(
% 2.17/0.98    v1_funct_1(sK2)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f38,plain,(
% 2.17/0.98    ~v2_struct_0(sK1)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f39,plain,(
% 2.17/0.98    v2_pre_topc(sK1)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f40,plain,(
% 2.17/0.98    l1_pre_topc(sK1)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f43,plain,(
% 2.17/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f1,axiom,(
% 2.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f7,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f1])).
% 2.17/0.98  
% 2.17/0.98  fof(f8,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.98    inference(flattening,[],[f7])).
% 2.17/0.98  
% 2.17/0.98  fof(f29,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f8])).
% 2.17/0.98  
% 2.17/0.98  fof(f35,plain,(
% 2.17/0.98    ~v2_struct_0(sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f36,plain,(
% 2.17/0.98    v2_pre_topc(sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f37,plain,(
% 2.17/0.98    l1_pre_topc(sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f4,axiom,(
% 2.17/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f13,plain,(
% 2.17/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.17/0.98    inference(ennf_transformation,[],[f4])).
% 2.17/0.98  
% 2.17/0.98  fof(f34,plain,(
% 2.17/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f13])).
% 2.17/0.98  
% 2.17/0.98  fof(f45,plain,(
% 2.17/0.98    m1_pre_topc(sK3,sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f48,plain,(
% 2.17/0.98    k1_tsep_1(sK0,sK3,sK4) = sK0),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f3,axiom,(
% 2.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) => ((X6 = X7 & X5 = X7) => (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))))))))))))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f11,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | (X6 != X7 | X5 != X7)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f3])).
% 2.17/0.98  
% 2.17/0.98  fof(f12,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.98    inference(flattening,[],[f11])).
% 2.17/0.98  
% 2.17/0.98  fof(f16,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | (~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) & ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.98    inference(nnf_transformation,[],[f12])).
% 2.17/0.98  
% 2.17/0.98  fof(f17,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) & ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.17/0.98    inference(flattening,[],[f16])).
% 2.17/0.98  
% 2.17/0.98  fof(f33,plain,(
% 2.17/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f57,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(equality_resolution,[],[f33])).
% 2.17/0.98  
% 2.17/0.98  fof(f58,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(equality_resolution,[],[f57])).
% 2.17/0.98  
% 2.17/0.98  fof(f44,plain,(
% 2.17/0.98    ~v2_struct_0(sK3)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f46,plain,(
% 2.17/0.98    ~v2_struct_0(sK4)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f31,plain,(
% 2.17/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f61,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(equality_resolution,[],[f31])).
% 2.17/0.98  
% 2.17/0.98  fof(f62,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(equality_resolution,[],[f61])).
% 2.17/0.98  
% 2.17/0.98  fof(f32,plain,(
% 2.17/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f59,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(equality_resolution,[],[f32])).
% 2.17/0.98  
% 2.17/0.98  fof(f60,plain,(
% 2.17/0.98    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.17/0.98    inference(equality_resolution,[],[f59])).
% 2.17/0.98  
% 2.17/0.98  fof(f56,plain,(
% 2.17/0.98    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f51,plain,(
% 2.17/0.98    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f49,plain,(
% 2.17/0.98    m1_subset_1(sK5,u1_struct_0(sK0))),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f50,plain,(
% 2.17/0.98    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f55,plain,(
% 2.17/0.98    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.17/0.98    inference(cnf_transformation,[],[f28])).
% 2.17/0.98  
% 2.17/0.98  cnf(c_8,negated_conjecture,
% 2.17/0.98      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.17/0.98      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 2.17/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_736,negated_conjecture,
% 2.17/0.98      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.17/0.98      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1196,plain,
% 2.17/0.98      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9,negated_conjecture,
% 2.17/0.98      ( sK5 = sK7 ),
% 2.17/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_735,negated_conjecture,
% 2.17/0.98      ( sK5 = sK7 ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_10,negated_conjecture,
% 2.17/0.98      ( sK5 = sK6 ),
% 2.17/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_734,negated_conjecture,
% 2.17/0.98      ( sK5 = sK6 ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1218,plain,
% 2.17/0.98      ( sK6 = sK7 ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_734,c_735]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1262,plain,
% 2.17/0.98      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_1196,c_735,c_1218]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_15,negated_conjecture,
% 2.17/0.98      ( m1_pre_topc(sK4,sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_729,negated_conjecture,
% 2.17/0.98      ( m1_pre_topc(sK4,sK0) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1200,plain,
% 2.17/0.98      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1,plain,
% 2.17/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.17/0.98      | ~ m1_pre_topc(X3,X4)
% 2.17/0.98      | ~ m1_pre_topc(X3,X1)
% 2.17/0.98      | ~ m1_pre_topc(X1,X4)
% 2.17/0.98      | v2_struct_0(X4)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ v2_pre_topc(X4)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X4)
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_20,negated_conjecture,
% 2.17/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_259,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.17/0.98      | ~ m1_pre_topc(X3,X1)
% 2.17/0.98      | ~ m1_pre_topc(X3,X4)
% 2.17/0.98      | ~ m1_pre_topc(X1,X4)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | v2_struct_0(X4)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ v2_pre_topc(X4)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X4)
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.17/0.98      | sK2 != X0 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_260,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_pre_topc(X2,X0)
% 2.17/0.98      | ~ m1_pre_topc(X2,X3)
% 2.17/0.98      | ~ m1_pre_topc(X0,X3)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X3)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X3)
% 2.17/0.98      | ~ v1_funct_1(sK2)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
% 2.17/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_259]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_21,negated_conjecture,
% 2.17/0.98      ( v1_funct_1(sK2) ),
% 2.17/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_264,plain,
% 2.17/0.98      ( ~ l1_pre_topc(X3)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X3)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | ~ m1_pre_topc(X0,X3)
% 2.17/0.98      | ~ m1_pre_topc(X2,X3)
% 2.17/0.98      | ~ m1_pre_topc(X2,X0)
% 2.17/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
% 2.17/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_260,c_21]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_265,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_pre_topc(X2,X0)
% 2.17/0.98      | ~ m1_pre_topc(X2,X3)
% 2.17/0.98      | ~ m1_pre_topc(X0,X3)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X3)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X3)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
% 2.17/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_264]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_718,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.17/0.98      | ~ m1_pre_topc(X2_51,X0_51)
% 2.17/0.98      | ~ m1_pre_topc(X2_51,X3_51)
% 2.17/0.98      | ~ m1_pre_topc(X0_51,X3_51)
% 2.17/0.98      | v2_struct_0(X1_51)
% 2.17/0.98      | v2_struct_0(X3_51)
% 2.17/0.98      | ~ v2_pre_topc(X1_51)
% 2.17/0.98      | ~ v2_pre_topc(X3_51)
% 2.17/0.98      | ~ l1_pre_topc(X1_51)
% 2.17/0.98      | ~ l1_pre_topc(X3_51)
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK2) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_265]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1211,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK2)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.98      | v2_struct_0(X3_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(X3_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X1_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X3_51) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1952,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.98      | v2_struct_0(sK1) = iProver_top
% 2.17/0.98      | v2_pre_topc(X2_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.98      | l1_pre_topc(X2_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.98      inference(equality_resolution,[status(thm)],[c_1211]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_24,negated_conjecture,
% 2.17/0.98      ( ~ v2_struct_0(sK1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_31,plain,
% 2.17/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_23,negated_conjecture,
% 2.17/0.98      ( v2_pre_topc(sK1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_32,plain,
% 2.17/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_22,negated_conjecture,
% 2.17/0.98      ( l1_pre_topc(sK1) ),
% 2.17/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_33,plain,
% 2.17/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_743,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1489,plain,
% 2.17/0.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_743]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1493,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 2.17/0.98      | ~ m1_pre_topc(X0_51,X1_51)
% 2.17/0.98      | ~ m1_pre_topc(X2_51,X0_51)
% 2.17/0.98      | ~ m1_pre_topc(X2_51,X1_51)
% 2.17/0.98      | v2_struct_0(X1_51)
% 2.17/0.98      | v2_struct_0(sK1)
% 2.17/0.98      | ~ v2_pre_topc(X1_51)
% 2.17/0.98      | ~ v2_pre_topc(sK1)
% 2.17/0.98      | ~ l1_pre_topc(X1_51)
% 2.17/0.98      | ~ l1_pre_topc(sK1)
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X1_51,sK1,X0_51,X2_51,sK2) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_718]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1499,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.98      | v2_struct_0(sK1) = iProver_top
% 2.17/0.98      | v2_pre_topc(X2_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.98      | l1_pre_topc(X2_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1493]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2541,plain,
% 2.17/0.98      ( l1_pre_topc(X2_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | v2_pre_topc(X2_51) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_1952,c_31,c_32,c_33,c_1489,c_1499]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2542,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X2_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X2_51) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_2541]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2556,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK0,X1_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X1_51) != iProver_top ),
% 2.17/0.98      inference(equality_resolution,[status(thm)],[c_2542]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_19,negated_conjecture,
% 2.17/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.17/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_36,plain,
% 2.17/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2689,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
% 2.17/0.98      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK0,X1_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X1_51) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2556,c_36]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2702,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)
% 2.17/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1200,c_2689]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_0,plain,
% 2.17/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.17/0.98      | ~ m1_pre_topc(X3,X1)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.17/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_310,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.17/0.98      | ~ m1_pre_topc(X3,X1)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ v1_funct_1(X0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.17/0.98      | sK2 != X0 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_311,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_pre_topc(X2,X0)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | ~ v2_pre_topc(X0)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X0)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ v1_funct_1(sK2)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
% 2.17/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_310]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_315,plain,
% 2.17/0.98      ( ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X0)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X0)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | ~ m1_pre_topc(X2,X0)
% 2.17/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
% 2.17/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_311,c_21]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_316,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_pre_topc(X2,X0)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X0)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
% 2.17/0.98      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_315]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_717,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 2.17/0.98      | ~ m1_pre_topc(X2_51,X0_51)
% 2.17/0.98      | v2_struct_0(X0_51)
% 2.17/0.98      | v2_struct_0(X1_51)
% 2.17/0.98      | ~ v2_pre_topc(X1_51)
% 2.17/0.98      | ~ v2_pre_topc(X0_51)
% 2.17/0.98      | ~ l1_pre_topc(X1_51)
% 2.17/0.98      | ~ l1_pre_topc(X0_51)
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_316]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1212,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X1_51) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2047,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_struct_0(sK1) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.98      inference(equality_resolution,[status(thm)],[c_1212]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1494,plain,
% 2.17/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 2.17/0.98      | ~ m1_pre_topc(X1_51,X0_51)
% 2.17/0.98      | v2_struct_0(X0_51)
% 2.17/0.98      | v2_struct_0(sK1)
% 2.17/0.98      | ~ v2_pre_topc(X0_51)
% 2.17/0.98      | ~ v2_pre_topc(sK1)
% 2.17/0.98      | ~ l1_pre_topc(X0_51)
% 2.17/0.98      | ~ l1_pre_topc(sK1)
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_717]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1495,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_struct_0(sK1) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1494]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2561,plain,
% 2.17/0.98      ( l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2047,c_31,c_32,c_33,c_1489,c_1495]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2562,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.17/0.98      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_2561]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2574,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X0_51,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(equality_resolution,[status(thm)],[c_2562]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_27,negated_conjecture,
% 2.17/0.98      ( ~ v2_struct_0(sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_28,plain,
% 2.17/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_26,negated_conjecture,
% 2.17/0.98      ( v2_pre_topc(sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_29,plain,
% 2.17/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_25,negated_conjecture,
% 2.17/0.98      ( l1_pre_topc(sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_30,plain,
% 2.17/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2642,plain,
% 2.17/0.98      ( m1_pre_topc(X0_51,sK0) != iProver_top
% 2.17/0.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2574,c_28,c_29,c_30,c_36]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2643,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
% 2.17/0.98      | m1_pre_topc(X0_51,sK0) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_2642]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2650,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1200,c_2643]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2736,plain,
% 2.17/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4)
% 2.17/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_2702,c_2650]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_40,plain,
% 2.17/0.98      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_5,plain,
% 2.17/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_47,plain,
% 2.17/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 2.17/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_49,plain,
% 2.17/0.98      ( m1_pre_topc(sK0,sK0) = iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_47]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2963,plain,
% 2.17/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2736,c_28,c_29,c_30,c_40,c_49]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_17,negated_conjecture,
% 2.17/0.98      ( m1_pre_topc(sK3,sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_727,negated_conjecture,
% 2.17/0.98      ( m1_pre_topc(sK3,sK0) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1202,plain,
% 2.17/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2703,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)
% 2.17/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1202,c_2689]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2651,plain,
% 2.17/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_1202,c_2643]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2723,plain,
% 2.17/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3)
% 2.17/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_2703,c_2651]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_38,plain,
% 2.17/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2829,plain,
% 2.17/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2723,c_28,c_29,c_30,c_38,c_49]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_14,negated_conjecture,
% 2.17/0.98      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 2.17/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_730,negated_conjecture,
% 2.17/0.98      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2,plain,
% 2.17/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 2.17/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X5)
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 2.17/0.98      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 2.17/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 2.17/0.98      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.17/0.98      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.98      | ~ m1_pre_topc(X0,X2)
% 2.17/0.98      | ~ m1_pre_topc(X3,X2)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ v1_funct_1(X4) ),
% 2.17/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_421,plain,
% 2.17/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 2.17/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X5)
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 2.17/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.17/0.98      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 2.17/0.98      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.98      | ~ m1_pre_topc(X3,X2)
% 2.17/0.98      | ~ m1_pre_topc(X0,X2)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ v1_funct_1(X4)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.98      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0)
% 2.17/0.98      | sK2 != X4 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_422,plain,
% 2.17/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 2.17/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_pre_topc(X0,X2)
% 2.17/0.98      | ~ m1_pre_topc(X3,X2)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ v1_funct_1(sK2)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.98      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_421]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_426,plain,
% 2.17/0.98      ( ~ l1_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | ~ m1_pre_topc(X3,X2)
% 2.17/0.98      | ~ m1_pre_topc(X0,X2)
% 2.17/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 2.17/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
% 2.17/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.98      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_422,c_21]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_427,plain,
% 2.17/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 2.17/0.98      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.98      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.98      | ~ m1_pre_topc(X3,X2)
% 2.17/0.98      | ~ m1_pre_topc(X0,X2)
% 2.17/0.98      | v2_struct_0(X0)
% 2.17/0.98      | v2_struct_0(X1)
% 2.17/0.98      | v2_struct_0(X2)
% 2.17/0.98      | v2_struct_0(X3)
% 2.17/0.98      | ~ v2_pre_topc(X1)
% 2.17/0.98      | ~ v2_pre_topc(X2)
% 2.17/0.98      | ~ l1_pre_topc(X1)
% 2.17/0.98      | ~ l1_pre_topc(X2)
% 2.17/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.98      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_426]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_715,plain,
% 2.17/0.98      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X0_51,sK2),X0_52)
% 2.17/0.98      | ~ r1_tmap_1(X3_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X3_51,sK2),X0_52)
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X2_51,X0_51,X3_51),X1_51,sK2,X0_52)
% 2.17/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 2.17/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.17/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)))
% 2.17/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)),u1_struct_0(X1_51))))
% 2.17/0.98      | ~ m1_pre_topc(X3_51,X2_51)
% 2.17/0.98      | ~ m1_pre_topc(X0_51,X2_51)
% 2.17/0.98      | v2_struct_0(X0_51)
% 2.17/0.98      | v2_struct_0(X1_51)
% 2.17/0.98      | v2_struct_0(X2_51)
% 2.17/0.98      | v2_struct_0(X3_51)
% 2.17/0.98      | ~ v2_pre_topc(X1_51)
% 2.17/0.98      | ~ v2_pre_topc(X2_51)
% 2.17/0.98      | ~ l1_pre_topc(X1_51)
% 2.17/0.98      | ~ l1_pre_topc(X2_51)
% 2.17/0.98      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.98      | u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)) != u1_struct_0(sK0) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_427]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1214,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.98      | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
% 2.17/0.98      | r1_tmap_1(X2_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X2_51,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(X3_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X3_51,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) = iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(X3_51,X1_51) != iProver_top
% 2.17/0.98      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.98      | v2_struct_0(X3_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X1_51) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2352,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.98      | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK3,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK4,sK2),X0_52) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_struct_0(sK3) = iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_struct_0(sK4) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_730,c_1214]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2353,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.98      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.98      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_struct_0(sK3) = iProver_top
% 2.17/0.98      | v2_struct_0(sK0) = iProver_top
% 2.17/0.98      | v2_struct_0(sK4) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_2352,c_730]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_18,negated_conjecture,
% 2.17/0.98      ( ~ v2_struct_0(sK3) ),
% 2.17/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_37,plain,
% 2.17/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_16,negated_conjecture,
% 2.17/0.98      ( ~ v2_struct_0(sK4) ),
% 2.17/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_39,plain,
% 2.17/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2424,plain,
% 2.17/0.98      ( l1_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.98      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
% 2.17/0.98      | u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top ),
% 2.17/0.98      inference(global_propositional_subsumption,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_2353,c_28,c_29,c_30,c_37,c_38,c_39,c_40]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2425,plain,
% 2.17/0.98      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.98      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.98      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.98      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.98      | l1_pre_topc(X0_51) != iProver_top ),
% 2.17/0.98      inference(renaming,[status(thm)],[c_2424]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2441,plain,
% 2.17/0.98      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
% 2.17/0.98      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 2.17/0.98      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.98      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.98      | v2_struct_0(sK1) = iProver_top
% 2.17/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.98      inference(equality_resolution,[status(thm)],[c_2425]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2446,plain,
% 2.17/0.98      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2441,c_31,c_32,c_33,c_36]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2832,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2829,c_2446]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2966,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2963,c_2832]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3333,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1262,c_2966]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,X4),X5)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,X4,X5)
% 2.17/0.99      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
% 2.17/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ v1_funct_1(X4) ),
% 2.17/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_490,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,X4),X5)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,X4,X5)
% 2.17/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ v1_funct_1(X4)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0)
% 2.17/0.99      | sK2 != X4 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_491,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ v1_funct_1(sK2)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_493,plain,
% 2.17/0.99      ( ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 2.17/0.99      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_491,c_21]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_494,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_493]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_714,plain,
% 2.17/0.99      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X0_51,sK2),X0_52)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_51,X0_51,X3_51),X1_51,sK2,X0_52)
% 2.17/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 2.17/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.17/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)))
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)),u1_struct_0(X1_51))))
% 2.17/0.99      | ~ m1_pre_topc(X3_51,X2_51)
% 2.17/0.99      | ~ m1_pre_topc(X0_51,X2_51)
% 2.17/0.99      | v2_struct_0(X0_51)
% 2.17/0.99      | v2_struct_0(X1_51)
% 2.17/0.99      | v2_struct_0(X2_51)
% 2.17/0.99      | v2_struct_0(X3_51)
% 2.17/0.99      | ~ v2_pre_topc(X1_51)
% 2.17/0.99      | ~ v2_pre_topc(X2_51)
% 2.17/0.99      | ~ l1_pre_topc(X1_51)
% 2.17/0.99      | ~ l1_pre_topc(X2_51)
% 2.17/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_494]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1215,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
% 2.17/0.99      | r1_tmap_1(X2_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X2_51,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_pre_topc(X3_51,X1_51) != iProver_top
% 2.17/0.99      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.17/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.99      | v2_struct_0(X3_51) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(X1_51) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2218,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK3,sK2),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_struct_0(sK3) = iProver_top
% 2.17/0.99      | v2_struct_0(sK0) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_730,c_1215]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2219,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_struct_0(sK3) = iProver_top
% 2.17/0.99      | v2_struct_0(sK0) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_2218,c_730]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2224,plain,
% 2.17/0.99      ( l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
% 2.17/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2219,c_28,c_29,c_30,c_37,c_38,c_39,c_40]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2225,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_2224]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2240,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.99      | v2_struct_0(sK1) = iProver_top
% 2.17/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.99      inference(equality_resolution,[status(thm)],[c_2225]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2321,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2240,c_31,c_32,c_33,c_36]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2833,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2829,c_2321]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 2.17/0.99      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 2.17/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ v1_funct_1(X4) ),
% 2.17/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_355,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 2.17/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ v1_funct_1(X4)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0)
% 2.17/0.99      | sK2 != X4 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_356,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ v1_funct_1(sK2)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_355]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_360,plain,
% 2.17/0.99      ( ~ l1_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
% 2.17/0.99      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_356,c_21]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_361,plain,
% 2.17/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.17/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 2.17/0.99      | ~ m1_pre_topc(X3,X2)
% 2.17/0.99      | ~ m1_pre_topc(X0,X2)
% 2.17/0.99      | v2_struct_0(X0)
% 2.17/0.99      | v2_struct_0(X1)
% 2.17/0.99      | v2_struct_0(X2)
% 2.17/0.99      | v2_struct_0(X3)
% 2.17/0.99      | ~ v2_pre_topc(X1)
% 2.17/0.99      | ~ v2_pre_topc(X2)
% 2.17/0.99      | ~ l1_pre_topc(X1)
% 2.17/0.99      | ~ l1_pre_topc(X2)
% 2.17/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_360]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_716,plain,
% 2.17/0.99      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X3_51,X0_51),X0_51,sK2),X0_52)
% 2.17/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_51,X3_51,X0_51),X1_51,sK2,X0_52)
% 2.17/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 2.17/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.17/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)))
% 2.17/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)),u1_struct_0(X1_51))))
% 2.17/0.99      | ~ m1_pre_topc(X3_51,X2_51)
% 2.17/0.99      | ~ m1_pre_topc(X0_51,X2_51)
% 2.17/0.99      | v2_struct_0(X0_51)
% 2.17/0.99      | v2_struct_0(X1_51)
% 2.17/0.99      | v2_struct_0(X2_51)
% 2.17/0.99      | v2_struct_0(X3_51)
% 2.17/0.99      | ~ v2_pre_topc(X1_51)
% 2.17/0.99      | ~ v2_pre_topc(X2_51)
% 2.17/0.99      | ~ l1_pre_topc(X1_51)
% 2.17/0.99      | ~ l1_pre_topc(X2_51)
% 2.17/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)) != u1_struct_0(sK0) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_361]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1213,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
% 2.17/0.99      | r1_tmap_1(X3_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X3_51,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.17/0.99      | m1_pre_topc(X3_51,X1_51) != iProver_top
% 2.17/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_struct_0(X3_51) = iProver_top
% 2.17/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(X1_51) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2070,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK4,sK2),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_struct_0(sK3) = iProver_top
% 2.17/0.99      | v2_struct_0(sK0) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_730,c_1213]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2071,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.17/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_struct_0(sK3) = iProver_top
% 2.17/0.99      | v2_struct_0(sK0) = iProver_top
% 2.17/0.99      | v2_struct_0(sK4) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_2070,c_730]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2125,plain,
% 2.17/0.99      ( l1_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2071,c_28,c_29,c_30,c_37,c_38,c_39,c_40]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2126,plain,
% 2.17/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 2.17/0.99      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 2.17/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.17/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.17/0.99      | l1_pre_topc(X0_51) != iProver_top ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_2125]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2141,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.17/0.99      | v2_struct_0(sK1) = iProver_top
% 2.17/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.17/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.17/0.99      inference(equality_resolution,[status(thm)],[c_2126]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2146,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2141,c_31,c_32,c_33,c_36]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2967,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) = iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2963,c_2146]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6,negated_conjecture,
% 2.17/0.99      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.17/0.99      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.17/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.17/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_738,negated_conjecture,
% 2.17/0.99      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.17/0.99      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.17/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1194,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1267,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_1194,c_735,c_1218]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3053,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_2967,c_1267]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_11,negated_conjecture,
% 2.17/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.17/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_43,plain,
% 2.17/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_13,negated_conjecture,
% 2.17/0.99      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 2.17/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_731,negated_conjecture,
% 2.17/0.99      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1199,plain,
% 2.17/0.99      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1246,plain,
% 2.17/0.99      ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_1199,c_735]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_12,negated_conjecture,
% 2.17/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.17/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_732,negated_conjecture,
% 2.17/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1198,plain,
% 2.17/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1243,plain,
% 2.17/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_1198,c_1218]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3056,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_3053,c_43,c_1246,c_1243]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3057,plain,
% 2.17/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.17/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_3056]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3063,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.17/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_2833,c_3057]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_7,negated_conjecture,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.17/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_737,negated_conjecture,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.17/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1195,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1257,plain,
% 2.17/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.17/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_1195,c_735]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(contradiction,plain,
% 2.17/0.99      ( $false ),
% 2.17/0.99      inference(minisat,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_3333,c_3063,c_1257,c_1243,c_1246,c_43]) ).
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  ------                               Statistics
% 2.17/0.99  
% 2.17/0.99  ------ General
% 2.17/0.99  
% 2.17/0.99  abstr_ref_over_cycles:                  0
% 2.17/0.99  abstr_ref_under_cycles:                 0
% 2.17/0.99  gc_basic_clause_elim:                   0
% 2.17/0.99  forced_gc_time:                         0
% 2.17/0.99  parsing_time:                           0.009
% 2.17/0.99  unif_index_cands_time:                  0.
% 2.17/0.99  unif_index_add_time:                    0.
% 2.17/0.99  orderings_time:                         0.
% 2.17/0.99  out_proof_time:                         0.017
% 2.17/0.99  total_time:                             0.167
% 2.17/0.99  num_of_symbols:                         55
% 2.17/0.99  num_of_terms:                           2941
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing
% 2.17/0.99  
% 2.17/0.99  num_of_splits:                          0
% 2.17/0.99  num_of_split_atoms:                     0
% 2.17/0.99  num_of_reused_defs:                     0
% 2.17/0.99  num_eq_ax_congr_red:                    11
% 2.17/0.99  num_of_sem_filtered_clauses:            1
% 2.17/0.99  num_of_subtypes:                        4
% 2.17/0.99  monotx_restored_types:                  0
% 2.17/0.99  sat_num_of_epr_types:                   0
% 2.17/0.99  sat_num_of_non_cyclic_types:            0
% 2.17/0.99  sat_guarded_non_collapsed_types:        0
% 2.17/0.99  num_pure_diseq_elim:                    0
% 2.17/0.99  simp_replaced_by:                       0
% 2.17/0.99  res_preprocessed:                       147
% 2.17/0.99  prep_upred:                             0
% 2.17/0.99  prep_unflattend:                        5
% 2.17/0.99  smt_new_axioms:                         0
% 2.17/0.99  pred_elim_cands:                        6
% 2.17/0.99  pred_elim:                              2
% 2.17/0.99  pred_elim_cl:                           2
% 2.17/0.99  pred_elim_cycles:                       4
% 2.17/0.99  merged_defs:                            0
% 2.17/0.99  merged_defs_ncl:                        0
% 2.17/0.99  bin_hyper_res:                          0
% 2.17/0.99  prep_cycles:                            4
% 2.17/0.99  pred_elim_time:                         0.012
% 2.17/0.99  splitting_time:                         0.
% 2.17/0.99  sem_filter_time:                        0.
% 2.17/0.99  monotx_time:                            0.
% 2.17/0.99  subtype_inf_time:                       0.001
% 2.17/0.99  
% 2.17/0.99  ------ Problem properties
% 2.17/0.99  
% 2.17/0.99  clauses:                                26
% 2.17/0.99  conjectures:                            20
% 2.17/0.99  epr:                                    13
% 2.17/0.99  horn:                                   19
% 2.17/0.99  ground:                                 20
% 2.17/0.99  unary:                                  17
% 2.17/0.99  binary:                                 3
% 2.17/0.99  lits:                                   105
% 2.17/0.99  lits_eq:                                15
% 2.17/0.99  fd_pure:                                0
% 2.17/0.99  fd_pseudo:                              0
% 2.17/0.99  fd_cond:                                0
% 2.17/0.99  fd_pseudo_cond:                         0
% 2.17/0.99  ac_symbols:                             0
% 2.17/0.99  
% 2.17/0.99  ------ Propositional Solver
% 2.17/0.99  
% 2.17/0.99  prop_solver_calls:                      28
% 2.17/0.99  prop_fast_solver_calls:                 1607
% 2.17/0.99  smt_solver_calls:                       0
% 2.17/0.99  smt_fast_solver_calls:                  0
% 2.17/0.99  prop_num_of_clauses:                    888
% 2.17/0.99  prop_preprocess_simplified:             3753
% 2.17/0.99  prop_fo_subsumed:                       70
% 2.17/0.99  prop_solver_time:                       0.
% 2.17/0.99  smt_solver_time:                        0.
% 2.17/0.99  smt_fast_solver_time:                   0.
% 2.17/0.99  prop_fast_solver_time:                  0.
% 2.17/0.99  prop_unsat_core_time:                   0.
% 2.17/0.99  
% 2.17/0.99  ------ QBF
% 2.17/0.99  
% 2.17/0.99  qbf_q_res:                              0
% 2.17/0.99  qbf_num_tautologies:                    0
% 2.17/0.99  qbf_prep_cycles:                        0
% 2.17/0.99  
% 2.17/0.99  ------ BMC1
% 2.17/0.99  
% 2.17/0.99  bmc1_current_bound:                     -1
% 2.17/0.99  bmc1_last_solved_bound:                 -1
% 2.17/0.99  bmc1_unsat_core_size:                   -1
% 2.17/0.99  bmc1_unsat_core_parents_size:           -1
% 2.17/0.99  bmc1_merge_next_fun:                    0
% 2.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation
% 2.17/0.99  
% 2.17/0.99  inst_num_of_clauses:                    298
% 2.17/0.99  inst_num_in_passive:                    6
% 2.17/0.99  inst_num_in_active:                     233
% 2.17/0.99  inst_num_in_unprocessed:                59
% 2.17/0.99  inst_num_of_loops:                      250
% 2.17/0.99  inst_num_of_learning_restarts:          0
% 2.17/0.99  inst_num_moves_active_passive:          11
% 2.17/0.99  inst_lit_activity:                      0
% 2.17/0.99  inst_lit_activity_moves:                0
% 2.17/0.99  inst_num_tautologies:                   0
% 2.17/0.99  inst_num_prop_implied:                  0
% 2.17/0.99  inst_num_existing_simplified:           0
% 2.17/0.99  inst_num_eq_res_simplified:             0
% 2.17/0.99  inst_num_child_elim:                    0
% 2.17/0.99  inst_num_of_dismatching_blockings:      101
% 2.17/0.99  inst_num_of_non_proper_insts:           345
% 2.17/0.99  inst_num_of_duplicates:                 0
% 2.17/0.99  inst_inst_num_from_inst_to_res:         0
% 2.17/0.99  inst_dismatching_checking_time:         0.
% 2.17/0.99  
% 2.17/0.99  ------ Resolution
% 2.17/0.99  
% 2.17/0.99  res_num_of_clauses:                     0
% 2.17/0.99  res_num_in_passive:                     0
% 2.17/0.99  res_num_in_active:                      0
% 2.17/0.99  res_num_of_loops:                       151
% 2.17/0.99  res_forward_subset_subsumed:            68
% 2.17/0.99  res_backward_subset_subsumed:           2
% 2.17/0.99  res_forward_subsumed:                   0
% 2.17/0.99  res_backward_subsumed:                  0
% 2.17/0.99  res_forward_subsumption_resolution:     0
% 2.17/0.99  res_backward_subsumption_resolution:    0
% 2.17/0.99  res_clause_to_clause_subsumption:       172
% 2.17/0.99  res_orphan_elimination:                 0
% 2.17/0.99  res_tautology_del:                      60
% 2.17/0.99  res_num_eq_res_simplified:              0
% 2.17/0.99  res_num_sel_changes:                    0
% 2.17/0.99  res_moves_from_active_to_pass:          0
% 2.17/0.99  
% 2.17/0.99  ------ Superposition
% 2.17/0.99  
% 2.17/0.99  sup_time_total:                         0.
% 2.17/0.99  sup_time_generating:                    0.
% 2.17/0.99  sup_time_sim_full:                      0.
% 2.17/0.99  sup_time_sim_immed:                     0.
% 2.17/0.99  
% 2.17/0.99  sup_num_of_clauses:                     47
% 2.17/0.99  sup_num_in_active:                      44
% 2.17/0.99  sup_num_in_passive:                     3
% 2.17/0.99  sup_num_of_loops:                       48
% 2.17/0.99  sup_fw_superposition:                   16
% 2.17/0.99  sup_bw_superposition:                   2
% 2.17/0.99  sup_immediate_simplified:               6
% 2.17/0.99  sup_given_eliminated:                   0
% 2.17/0.99  comparisons_done:                       0
% 2.17/0.99  comparisons_avoided:                    0
% 2.17/0.99  
% 2.17/0.99  ------ Simplifications
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  sim_fw_subset_subsumed:                 0
% 2.17/0.99  sim_bw_subset_subsumed:                 2
% 2.17/0.99  sim_fw_subsumed:                        0
% 2.17/0.99  sim_bw_subsumed:                        0
% 2.17/0.99  sim_fw_subsumption_res:                 0
% 2.17/0.99  sim_bw_subsumption_res:                 0
% 2.17/0.99  sim_tautology_del:                      5
% 2.17/0.99  sim_eq_tautology_del:                   0
% 2.17/0.99  sim_eq_res_simp:                        0
% 2.17/0.99  sim_fw_demodulated:                     0
% 2.17/0.99  sim_bw_demodulated:                     4
% 2.17/0.99  sim_light_normalised:                   12
% 2.17/0.99  sim_joinable_taut:                      0
% 2.17/0.99  sim_joinable_simp:                      0
% 2.17/0.99  sim_ac_normalised:                      0
% 2.17/0.99  sim_smt_subsumption:                    0
% 2.17/0.99  
%------------------------------------------------------------------------------
