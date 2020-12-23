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
% DateTime   : Thu Dec  3 12:24:16 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  213 (3651 expanded)
%              Number of clauses        :  149 ( 615 expanded)
%              Number of leaves         :   14 (1678 expanded)
%              Depth                    :   29
%              Number of atoms          : 1939 (80570 expanded)
%              Number of equality atoms :  681 (13112 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f29,f28,f27,f26,f25,f24,f23,f22])).

fof(f57,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
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
    inference(equality_resolution,[],[f37])).

fof(f61,plain,(
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
    inference(equality_resolution,[],[f60])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
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
    inference(equality_resolution,[],[f35])).

fof(f65,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f36])).

fof(f63,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f59,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_751,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1225,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_10,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_750,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_11,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_749,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1247,plain,
    ( sK6 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_749,c_750])).

cnf(c_1287,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1225,c_750,c_1247])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_744,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1229,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

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
    inference(cnf_transformation,[],[f32])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_269,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_270,plain,
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
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_274,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_22])).

cnf(c_275,plain,
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
    inference(renaming,[status(thm)],[c_274])).

cnf(c_733,plain,
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
    inference(subtyping,[status(esa)],[c_275])).

cnf(c_1240,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_2154,plain,
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
    inference(equality_resolution,[status(thm)],[c_1240])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_759,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1544,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1548,plain,
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
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1554,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_2750,plain,
    ( l1_pre_topc(X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_32,c_33,c_34,c_1544,c_1554])).

cnf(c_2751,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2750])).

cnf(c_2765,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2751])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3048,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2765,c_37])).

cnf(c_3061,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_3048])).

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
    inference(cnf_transformation,[],[f31])).

cnf(c_320,plain,
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
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_321,plain,
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
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_325,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_22])).

cnf(c_326,plain,
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
    inference(renaming,[status(thm)],[c_325])).

cnf(c_732,plain,
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
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_1241,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(X1_51) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_2086,plain,
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
    inference(equality_resolution,[status(thm)],[c_1241])).

cnf(c_1549,plain,
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
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1550,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_2638,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2086,c_32,c_33,c_34,c_1544,c_1550])).

cnf(c_2639,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2638])).

cnf(c_2651,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2639])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_29,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_30,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_31,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2864,plain,
    ( m1_pre_topc(X0_51,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2651,c_29,c_30,c_31,c_37])).

cnf(c_2865,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
    | m1_pre_topc(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2864])).

cnf(c_2872,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1229,c_2865])).

cnf(c_3115,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3061,c_2872])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_40,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_41,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_745,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_755,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | m1_pre_topc(k1_tsep_1(X1_51,X2_51,X0_51),X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1221,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_51,X2_51,X0_51),X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_1655,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) = iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_1221])).

cnf(c_4830,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3115,c_29,c_30,c_31,c_38,c_39,c_40,c_41,c_1655])).

cnf(c_742,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1231,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_3062,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_3048])).

cnf(c_2873,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1231,c_2865])).

cnf(c_3102,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3062,c_2873])).

cnf(c_3203,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3102,c_29,c_30,c_31,c_38,c_39,c_40,c_41,c_1655])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_431,plain,
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
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_432,plain,
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
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_436,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_22])).

cnf(c_437,plain,
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
    inference(renaming,[status(thm)],[c_436])).

cnf(c_730,plain,
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
    inference(subtyping,[status(esa)],[c_437])).

cnf(c_1243,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_2539,plain,
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
    inference(superposition,[status(thm)],[c_745,c_1243])).

cnf(c_2540,plain,
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
    inference(light_normalisation,[status(thm)],[c_2539,c_745])).

cnf(c_2616,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2540,c_29,c_30,c_31,c_38,c_39,c_40,c_41])).

cnf(c_2617,plain,
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
    inference(renaming,[status(thm)],[c_2616])).

cnf(c_2633,plain,
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
    inference(equality_resolution,[status(thm)],[c_2617])).

cnf(c_2735,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2633,c_32,c_33,c_34,c_37])).

cnf(c_3206,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3203,c_2735])).

cnf(c_4833,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4830,c_3206])).

cnf(c_13964,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_4833])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_500,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_501,plain,
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
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_503,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_22])).

cnf(c_504,plain,
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
    inference(renaming,[status(thm)],[c_503])).

cnf(c_729,plain,
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
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_1244,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_2361,plain,
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
    inference(superposition,[status(thm)],[c_745,c_1244])).

cnf(c_2362,plain,
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
    inference(light_normalisation,[status(thm)],[c_2361,c_745])).

cnf(c_2367,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_29,c_30,c_31,c_38,c_39,c_40,c_41])).

cnf(c_2368,plain,
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
    inference(renaming,[status(thm)],[c_2367])).

cnf(c_2383,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2368])).

cnf(c_2508,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2383,c_32,c_33,c_34,c_37])).

cnf(c_3207,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3203,c_2508])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_365,plain,
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
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_366,plain,
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
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_22])).

cnf(c_371,plain,
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
    inference(renaming,[status(thm)],[c_370])).

cnf(c_731,plain,
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
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_1242,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2177,plain,
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
    inference(superposition,[status(thm)],[c_745,c_1242])).

cnf(c_2178,plain,
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
    inference(light_normalisation,[status(thm)],[c_2177,c_745])).

cnf(c_2237,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2178,c_29,c_30,c_31,c_38,c_39,c_40,c_41])).

cnf(c_2238,plain,
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
    inference(renaming,[status(thm)],[c_2237])).

cnf(c_2253,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2238])).

cnf(c_2258,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2253,c_32,c_33,c_34,c_37])).

cnf(c_4834,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4830,c_2258])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_753,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1223,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_1292,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1223,c_750,c_1247])).

cnf(c_8744,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_1292])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_44,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_746,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1228,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_1275,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1228,c_750])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_747,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1227,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_1272,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1227,c_1247])).

cnf(c_8747,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8744,c_44,c_1275,c_1272])).

cnf(c_8748,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_8747])).

cnf(c_8754,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_8748])).

cnf(c_8,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_752,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1224,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_1282,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1224,c_750])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13964,c_8754,c_1272,c_1275,c_1282,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.45/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.02  
% 3.45/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/1.02  
% 3.45/1.02  ------  iProver source info
% 3.45/1.02  
% 3.45/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.45/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/1.02  git: non_committed_changes: false
% 3.45/1.02  git: last_make_outside_of_git: false
% 3.45/1.02  
% 3.45/1.02  ------ 
% 3.45/1.02  
% 3.45/1.02  ------ Input Options
% 3.45/1.02  
% 3.45/1.02  --out_options                           all
% 3.45/1.02  --tptp_safe_out                         true
% 3.45/1.02  --problem_path                          ""
% 3.45/1.02  --include_path                          ""
% 3.45/1.02  --clausifier                            res/vclausify_rel
% 3.45/1.02  --clausifier_options                    --mode clausify
% 3.45/1.02  --stdin                                 false
% 3.45/1.02  --stats_out                             all
% 3.45/1.02  
% 3.45/1.02  ------ General Options
% 3.45/1.02  
% 3.45/1.02  --fof                                   false
% 3.45/1.02  --time_out_real                         305.
% 3.45/1.02  --time_out_virtual                      -1.
% 3.45/1.02  --symbol_type_check                     false
% 3.45/1.02  --clausify_out                          false
% 3.45/1.02  --sig_cnt_out                           false
% 3.45/1.02  --trig_cnt_out                          false
% 3.45/1.02  --trig_cnt_out_tolerance                1.
% 3.45/1.02  --trig_cnt_out_sk_spl                   false
% 3.45/1.02  --abstr_cl_out                          false
% 3.45/1.02  
% 3.45/1.02  ------ Global Options
% 3.45/1.02  
% 3.45/1.02  --schedule                              default
% 3.45/1.02  --add_important_lit                     false
% 3.45/1.02  --prop_solver_per_cl                    1000
% 3.45/1.02  --min_unsat_core                        false
% 3.45/1.02  --soft_assumptions                      false
% 3.45/1.02  --soft_lemma_size                       3
% 3.45/1.02  --prop_impl_unit_size                   0
% 3.45/1.02  --prop_impl_unit                        []
% 3.45/1.02  --share_sel_clauses                     true
% 3.45/1.02  --reset_solvers                         false
% 3.45/1.02  --bc_imp_inh                            [conj_cone]
% 3.45/1.02  --conj_cone_tolerance                   3.
% 3.45/1.02  --extra_neg_conj                        none
% 3.45/1.02  --large_theory_mode                     true
% 3.45/1.02  --prolific_symb_bound                   200
% 3.45/1.02  --lt_threshold                          2000
% 3.45/1.02  --clause_weak_htbl                      true
% 3.45/1.02  --gc_record_bc_elim                     false
% 3.45/1.02  
% 3.45/1.02  ------ Preprocessing Options
% 3.45/1.02  
% 3.45/1.02  --preprocessing_flag                    true
% 3.45/1.02  --time_out_prep_mult                    0.1
% 3.45/1.02  --splitting_mode                        input
% 3.45/1.02  --splitting_grd                         true
% 3.45/1.02  --splitting_cvd                         false
% 3.45/1.02  --splitting_cvd_svl                     false
% 3.45/1.02  --splitting_nvd                         32
% 3.45/1.02  --sub_typing                            true
% 3.45/1.02  --prep_gs_sim                           true
% 3.45/1.02  --prep_unflatten                        true
% 3.45/1.02  --prep_res_sim                          true
% 3.45/1.02  --prep_upred                            true
% 3.45/1.02  --prep_sem_filter                       exhaustive
% 3.45/1.02  --prep_sem_filter_out                   false
% 3.45/1.02  --pred_elim                             true
% 3.45/1.02  --res_sim_input                         true
% 3.45/1.02  --eq_ax_congr_red                       true
% 3.45/1.02  --pure_diseq_elim                       true
% 3.45/1.02  --brand_transform                       false
% 3.45/1.02  --non_eq_to_eq                          false
% 3.45/1.02  --prep_def_merge                        true
% 3.45/1.02  --prep_def_merge_prop_impl              false
% 3.45/1.02  --prep_def_merge_mbd                    true
% 3.45/1.02  --prep_def_merge_tr_red                 false
% 3.45/1.02  --prep_def_merge_tr_cl                  false
% 3.45/1.02  --smt_preprocessing                     true
% 3.45/1.02  --smt_ac_axioms                         fast
% 3.45/1.02  --preprocessed_out                      false
% 3.45/1.02  --preprocessed_stats                    false
% 3.45/1.02  
% 3.45/1.02  ------ Abstraction refinement Options
% 3.45/1.02  
% 3.45/1.02  --abstr_ref                             []
% 3.45/1.02  --abstr_ref_prep                        false
% 3.45/1.02  --abstr_ref_until_sat                   false
% 3.45/1.02  --abstr_ref_sig_restrict                funpre
% 3.45/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.02  --abstr_ref_under                       []
% 3.45/1.02  
% 3.45/1.02  ------ SAT Options
% 3.45/1.02  
% 3.45/1.02  --sat_mode                              false
% 3.45/1.02  --sat_fm_restart_options                ""
% 3.45/1.02  --sat_gr_def                            false
% 3.45/1.02  --sat_epr_types                         true
% 3.45/1.02  --sat_non_cyclic_types                  false
% 3.45/1.02  --sat_finite_models                     false
% 3.45/1.02  --sat_fm_lemmas                         false
% 3.45/1.02  --sat_fm_prep                           false
% 3.45/1.02  --sat_fm_uc_incr                        true
% 3.45/1.02  --sat_out_model                         small
% 3.45/1.02  --sat_out_clauses                       false
% 3.45/1.02  
% 3.45/1.02  ------ QBF Options
% 3.45/1.02  
% 3.45/1.02  --qbf_mode                              false
% 3.45/1.02  --qbf_elim_univ                         false
% 3.45/1.02  --qbf_dom_inst                          none
% 3.45/1.02  --qbf_dom_pre_inst                      false
% 3.45/1.02  --qbf_sk_in                             false
% 3.45/1.02  --qbf_pred_elim                         true
% 3.45/1.02  --qbf_split                             512
% 3.45/1.02  
% 3.45/1.02  ------ BMC1 Options
% 3.45/1.02  
% 3.45/1.02  --bmc1_incremental                      false
% 3.45/1.02  --bmc1_axioms                           reachable_all
% 3.45/1.02  --bmc1_min_bound                        0
% 3.45/1.02  --bmc1_max_bound                        -1
% 3.45/1.02  --bmc1_max_bound_default                -1
% 3.45/1.02  --bmc1_symbol_reachability              true
% 3.45/1.02  --bmc1_property_lemmas                  false
% 3.45/1.02  --bmc1_k_induction                      false
% 3.45/1.02  --bmc1_non_equiv_states                 false
% 3.45/1.02  --bmc1_deadlock                         false
% 3.45/1.02  --bmc1_ucm                              false
% 3.45/1.02  --bmc1_add_unsat_core                   none
% 3.45/1.02  --bmc1_unsat_core_children              false
% 3.45/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.02  --bmc1_out_stat                         full
% 3.45/1.02  --bmc1_ground_init                      false
% 3.45/1.02  --bmc1_pre_inst_next_state              false
% 3.45/1.02  --bmc1_pre_inst_state                   false
% 3.45/1.02  --bmc1_pre_inst_reach_state             false
% 3.45/1.02  --bmc1_out_unsat_core                   false
% 3.45/1.02  --bmc1_aig_witness_out                  false
% 3.45/1.02  --bmc1_verbose                          false
% 3.45/1.02  --bmc1_dump_clauses_tptp                false
% 3.45/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.02  --bmc1_dump_file                        -
% 3.45/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.02  --bmc1_ucm_extend_mode                  1
% 3.45/1.02  --bmc1_ucm_init_mode                    2
% 3.45/1.02  --bmc1_ucm_cone_mode                    none
% 3.45/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.02  --bmc1_ucm_relax_model                  4
% 3.45/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.02  --bmc1_ucm_layered_model                none
% 3.45/1.02  --bmc1_ucm_max_lemma_size               10
% 3.45/1.02  
% 3.45/1.02  ------ AIG Options
% 3.45/1.02  
% 3.45/1.02  --aig_mode                              false
% 3.45/1.02  
% 3.45/1.02  ------ Instantiation Options
% 3.45/1.02  
% 3.45/1.02  --instantiation_flag                    true
% 3.45/1.02  --inst_sos_flag                         false
% 3.45/1.02  --inst_sos_phase                        true
% 3.45/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.02  --inst_lit_sel_side                     num_symb
% 3.45/1.02  --inst_solver_per_active                1400
% 3.45/1.02  --inst_solver_calls_frac                1.
% 3.45/1.02  --inst_passive_queue_type               priority_queues
% 3.45/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.02  --inst_passive_queues_freq              [25;2]
% 3.45/1.02  --inst_dismatching                      true
% 3.45/1.02  --inst_eager_unprocessed_to_passive     true
% 3.45/1.02  --inst_prop_sim_given                   true
% 3.45/1.02  --inst_prop_sim_new                     false
% 3.45/1.02  --inst_subs_new                         false
% 3.45/1.02  --inst_eq_res_simp                      false
% 3.45/1.02  --inst_subs_given                       false
% 3.45/1.02  --inst_orphan_elimination               true
% 3.45/1.02  --inst_learning_loop_flag               true
% 3.45/1.02  --inst_learning_start                   3000
% 3.45/1.02  --inst_learning_factor                  2
% 3.45/1.02  --inst_start_prop_sim_after_learn       3
% 3.45/1.02  --inst_sel_renew                        solver
% 3.45/1.02  --inst_lit_activity_flag                true
% 3.45/1.02  --inst_restr_to_given                   false
% 3.45/1.02  --inst_activity_threshold               500
% 3.45/1.02  --inst_out_proof                        true
% 3.45/1.02  
% 3.45/1.02  ------ Resolution Options
% 3.45/1.02  
% 3.45/1.02  --resolution_flag                       true
% 3.45/1.02  --res_lit_sel                           adaptive
% 3.45/1.02  --res_lit_sel_side                      none
% 3.45/1.02  --res_ordering                          kbo
% 3.45/1.02  --res_to_prop_solver                    active
% 3.45/1.02  --res_prop_simpl_new                    false
% 3.45/1.02  --res_prop_simpl_given                  true
% 3.45/1.02  --res_passive_queue_type                priority_queues
% 3.45/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.02  --res_passive_queues_freq               [15;5]
% 3.45/1.02  --res_forward_subs                      full
% 3.45/1.02  --res_backward_subs                     full
% 3.45/1.02  --res_forward_subs_resolution           true
% 3.45/1.02  --res_backward_subs_resolution          true
% 3.45/1.02  --res_orphan_elimination                true
% 3.45/1.02  --res_time_limit                        2.
% 3.45/1.02  --res_out_proof                         true
% 3.45/1.02  
% 3.45/1.02  ------ Superposition Options
% 3.45/1.02  
% 3.45/1.02  --superposition_flag                    true
% 3.45/1.02  --sup_passive_queue_type                priority_queues
% 3.45/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.02  --demod_completeness_check              fast
% 3.45/1.02  --demod_use_ground                      true
% 3.45/1.02  --sup_to_prop_solver                    passive
% 3.45/1.02  --sup_prop_simpl_new                    true
% 3.45/1.02  --sup_prop_simpl_given                  true
% 3.45/1.02  --sup_fun_splitting                     false
% 3.45/1.02  --sup_smt_interval                      50000
% 3.45/1.02  
% 3.45/1.02  ------ Superposition Simplification Setup
% 3.45/1.02  
% 3.45/1.02  --sup_indices_passive                   []
% 3.45/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.02  --sup_full_bw                           [BwDemod]
% 3.45/1.02  --sup_immed_triv                        [TrivRules]
% 3.45/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.02  --sup_immed_bw_main                     []
% 3.45/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.02  
% 3.45/1.02  ------ Combination Options
% 3.45/1.02  
% 3.45/1.02  --comb_res_mult                         3
% 3.45/1.02  --comb_sup_mult                         2
% 3.45/1.02  --comb_inst_mult                        10
% 3.45/1.02  
% 3.45/1.02  ------ Debug Options
% 3.45/1.02  
% 3.45/1.02  --dbg_backtrace                         false
% 3.45/1.02  --dbg_dump_prop_clauses                 false
% 3.45/1.02  --dbg_dump_prop_clauses_file            -
% 3.45/1.02  --dbg_out_stat                          false
% 3.45/1.02  ------ Parsing...
% 3.45/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/1.02  
% 3.45/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.45/1.02  
% 3.45/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/1.02  
% 3.45/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/1.02  ------ Proving...
% 3.45/1.02  ------ Problem Properties 
% 3.45/1.02  
% 3.45/1.02  
% 3.45/1.02  clauses                                 27
% 3.45/1.02  conjectures                             20
% 3.45/1.02  EPR                                     12
% 3.45/1.02  Horn                                    18
% 3.45/1.02  unary                                   17
% 3.45/1.02  binary                                  2
% 3.45/1.02  lits                                    117
% 3.45/1.02  lits eq                                 15
% 3.45/1.02  fd_pure                                 0
% 3.45/1.02  fd_pseudo                               0
% 3.45/1.02  fd_cond                                 0
% 3.45/1.02  fd_pseudo_cond                          0
% 3.45/1.02  AC symbols                              0
% 3.45/1.02  
% 3.45/1.02  ------ Schedule dynamic 5 is on 
% 3.45/1.02  
% 3.45/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/1.02  
% 3.45/1.02  
% 3.45/1.02  ------ 
% 3.45/1.02  Current options:
% 3.45/1.02  ------ 
% 3.45/1.02  
% 3.45/1.02  ------ Input Options
% 3.45/1.02  
% 3.45/1.02  --out_options                           all
% 3.45/1.02  --tptp_safe_out                         true
% 3.45/1.02  --problem_path                          ""
% 3.45/1.02  --include_path                          ""
% 3.45/1.02  --clausifier                            res/vclausify_rel
% 3.45/1.02  --clausifier_options                    --mode clausify
% 3.45/1.02  --stdin                                 false
% 3.45/1.02  --stats_out                             all
% 3.45/1.02  
% 3.45/1.02  ------ General Options
% 3.45/1.02  
% 3.45/1.02  --fof                                   false
% 3.45/1.02  --time_out_real                         305.
% 3.45/1.02  --time_out_virtual                      -1.
% 3.45/1.02  --symbol_type_check                     false
% 3.45/1.02  --clausify_out                          false
% 3.45/1.02  --sig_cnt_out                           false
% 3.45/1.02  --trig_cnt_out                          false
% 3.45/1.02  --trig_cnt_out_tolerance                1.
% 3.45/1.02  --trig_cnt_out_sk_spl                   false
% 3.45/1.02  --abstr_cl_out                          false
% 3.45/1.02  
% 3.45/1.02  ------ Global Options
% 3.45/1.02  
% 3.45/1.02  --schedule                              default
% 3.45/1.02  --add_important_lit                     false
% 3.45/1.02  --prop_solver_per_cl                    1000
% 3.45/1.02  --min_unsat_core                        false
% 3.45/1.02  --soft_assumptions                      false
% 3.45/1.02  --soft_lemma_size                       3
% 3.45/1.02  --prop_impl_unit_size                   0
% 3.45/1.02  --prop_impl_unit                        []
% 3.45/1.02  --share_sel_clauses                     true
% 3.45/1.02  --reset_solvers                         false
% 3.45/1.02  --bc_imp_inh                            [conj_cone]
% 3.45/1.02  --conj_cone_tolerance                   3.
% 3.45/1.02  --extra_neg_conj                        none
% 3.45/1.02  --large_theory_mode                     true
% 3.45/1.02  --prolific_symb_bound                   200
% 3.45/1.02  --lt_threshold                          2000
% 3.45/1.02  --clause_weak_htbl                      true
% 3.45/1.02  --gc_record_bc_elim                     false
% 3.45/1.02  
% 3.45/1.02  ------ Preprocessing Options
% 3.45/1.02  
% 3.45/1.02  --preprocessing_flag                    true
% 3.45/1.02  --time_out_prep_mult                    0.1
% 3.45/1.02  --splitting_mode                        input
% 3.45/1.02  --splitting_grd                         true
% 3.45/1.02  --splitting_cvd                         false
% 3.45/1.02  --splitting_cvd_svl                     false
% 3.45/1.02  --splitting_nvd                         32
% 3.45/1.02  --sub_typing                            true
% 3.45/1.02  --prep_gs_sim                           true
% 3.45/1.02  --prep_unflatten                        true
% 3.45/1.02  --prep_res_sim                          true
% 3.45/1.02  --prep_upred                            true
% 3.45/1.02  --prep_sem_filter                       exhaustive
% 3.45/1.02  --prep_sem_filter_out                   false
% 3.45/1.02  --pred_elim                             true
% 3.45/1.02  --res_sim_input                         true
% 3.45/1.02  --eq_ax_congr_red                       true
% 3.45/1.02  --pure_diseq_elim                       true
% 3.45/1.02  --brand_transform                       false
% 3.45/1.02  --non_eq_to_eq                          false
% 3.45/1.02  --prep_def_merge                        true
% 3.45/1.02  --prep_def_merge_prop_impl              false
% 3.45/1.02  --prep_def_merge_mbd                    true
% 3.45/1.02  --prep_def_merge_tr_red                 false
% 3.45/1.02  --prep_def_merge_tr_cl                  false
% 3.45/1.02  --smt_preprocessing                     true
% 3.45/1.02  --smt_ac_axioms                         fast
% 3.45/1.02  --preprocessed_out                      false
% 3.45/1.02  --preprocessed_stats                    false
% 3.45/1.02  
% 3.45/1.02  ------ Abstraction refinement Options
% 3.45/1.02  
% 3.45/1.02  --abstr_ref                             []
% 3.45/1.02  --abstr_ref_prep                        false
% 3.45/1.02  --abstr_ref_until_sat                   false
% 3.45/1.02  --abstr_ref_sig_restrict                funpre
% 3.45/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/1.02  --abstr_ref_under                       []
% 3.45/1.02  
% 3.45/1.02  ------ SAT Options
% 3.45/1.02  
% 3.45/1.02  --sat_mode                              false
% 3.45/1.02  --sat_fm_restart_options                ""
% 3.45/1.02  --sat_gr_def                            false
% 3.45/1.02  --sat_epr_types                         true
% 3.45/1.02  --sat_non_cyclic_types                  false
% 3.45/1.02  --sat_finite_models                     false
% 3.45/1.02  --sat_fm_lemmas                         false
% 3.45/1.02  --sat_fm_prep                           false
% 3.45/1.02  --sat_fm_uc_incr                        true
% 3.45/1.02  --sat_out_model                         small
% 3.45/1.02  --sat_out_clauses                       false
% 3.45/1.02  
% 3.45/1.02  ------ QBF Options
% 3.45/1.02  
% 3.45/1.02  --qbf_mode                              false
% 3.45/1.02  --qbf_elim_univ                         false
% 3.45/1.02  --qbf_dom_inst                          none
% 3.45/1.02  --qbf_dom_pre_inst                      false
% 3.45/1.02  --qbf_sk_in                             false
% 3.45/1.02  --qbf_pred_elim                         true
% 3.45/1.02  --qbf_split                             512
% 3.45/1.02  
% 3.45/1.02  ------ BMC1 Options
% 3.45/1.02  
% 3.45/1.02  --bmc1_incremental                      false
% 3.45/1.02  --bmc1_axioms                           reachable_all
% 3.45/1.02  --bmc1_min_bound                        0
% 3.45/1.02  --bmc1_max_bound                        -1
% 3.45/1.02  --bmc1_max_bound_default                -1
% 3.45/1.02  --bmc1_symbol_reachability              true
% 3.45/1.02  --bmc1_property_lemmas                  false
% 3.45/1.02  --bmc1_k_induction                      false
% 3.45/1.02  --bmc1_non_equiv_states                 false
% 3.45/1.02  --bmc1_deadlock                         false
% 3.45/1.02  --bmc1_ucm                              false
% 3.45/1.02  --bmc1_add_unsat_core                   none
% 3.45/1.02  --bmc1_unsat_core_children              false
% 3.45/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.02  --bmc1_out_stat                         full
% 3.45/1.02  --bmc1_ground_init                      false
% 3.45/1.02  --bmc1_pre_inst_next_state              false
% 3.45/1.02  --bmc1_pre_inst_state                   false
% 3.45/1.02  --bmc1_pre_inst_reach_state             false
% 3.45/1.02  --bmc1_out_unsat_core                   false
% 3.45/1.02  --bmc1_aig_witness_out                  false
% 3.45/1.02  --bmc1_verbose                          false
% 3.45/1.02  --bmc1_dump_clauses_tptp                false
% 3.45/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.02  --bmc1_dump_file                        -
% 3.45/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.02  --bmc1_ucm_extend_mode                  1
% 3.45/1.02  --bmc1_ucm_init_mode                    2
% 3.45/1.02  --bmc1_ucm_cone_mode                    none
% 3.45/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.02  --bmc1_ucm_relax_model                  4
% 3.45/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.02  --bmc1_ucm_layered_model                none
% 3.45/1.02  --bmc1_ucm_max_lemma_size               10
% 3.45/1.02  
% 3.45/1.02  ------ AIG Options
% 3.45/1.02  
% 3.45/1.02  --aig_mode                              false
% 3.45/1.02  
% 3.45/1.02  ------ Instantiation Options
% 3.45/1.02  
% 3.45/1.02  --instantiation_flag                    true
% 3.45/1.02  --inst_sos_flag                         false
% 3.45/1.02  --inst_sos_phase                        true
% 3.45/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.02  --inst_lit_sel_side                     none
% 3.45/1.02  --inst_solver_per_active                1400
% 3.45/1.02  --inst_solver_calls_frac                1.
% 3.45/1.02  --inst_passive_queue_type               priority_queues
% 3.45/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.02  --inst_passive_queues_freq              [25;2]
% 3.45/1.02  --inst_dismatching                      true
% 3.45/1.02  --inst_eager_unprocessed_to_passive     true
% 3.45/1.02  --inst_prop_sim_given                   true
% 3.45/1.02  --inst_prop_sim_new                     false
% 3.45/1.02  --inst_subs_new                         false
% 3.45/1.02  --inst_eq_res_simp                      false
% 3.45/1.02  --inst_subs_given                       false
% 3.45/1.02  --inst_orphan_elimination               true
% 3.45/1.02  --inst_learning_loop_flag               true
% 3.45/1.02  --inst_learning_start                   3000
% 3.45/1.02  --inst_learning_factor                  2
% 3.45/1.02  --inst_start_prop_sim_after_learn       3
% 3.45/1.02  --inst_sel_renew                        solver
% 3.45/1.02  --inst_lit_activity_flag                true
% 3.45/1.02  --inst_restr_to_given                   false
% 3.45/1.02  --inst_activity_threshold               500
% 3.45/1.02  --inst_out_proof                        true
% 3.45/1.02  
% 3.45/1.02  ------ Resolution Options
% 3.45/1.02  
% 3.45/1.02  --resolution_flag                       false
% 3.45/1.02  --res_lit_sel                           adaptive
% 3.45/1.02  --res_lit_sel_side                      none
% 3.45/1.02  --res_ordering                          kbo
% 3.45/1.02  --res_to_prop_solver                    active
% 3.45/1.02  --res_prop_simpl_new                    false
% 3.45/1.02  --res_prop_simpl_given                  true
% 3.45/1.02  --res_passive_queue_type                priority_queues
% 3.45/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.02  --res_passive_queues_freq               [15;5]
% 3.45/1.02  --res_forward_subs                      full
% 3.45/1.02  --res_backward_subs                     full
% 3.45/1.02  --res_forward_subs_resolution           true
% 3.45/1.02  --res_backward_subs_resolution          true
% 3.45/1.02  --res_orphan_elimination                true
% 3.45/1.02  --res_time_limit                        2.
% 3.45/1.02  --res_out_proof                         true
% 3.45/1.02  
% 3.45/1.02  ------ Superposition Options
% 3.45/1.02  
% 3.45/1.02  --superposition_flag                    true
% 3.45/1.02  --sup_passive_queue_type                priority_queues
% 3.45/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.02  --demod_completeness_check              fast
% 3.45/1.02  --demod_use_ground                      true
% 3.45/1.02  --sup_to_prop_solver                    passive
% 3.45/1.02  --sup_prop_simpl_new                    true
% 3.45/1.02  --sup_prop_simpl_given                  true
% 3.45/1.02  --sup_fun_splitting                     false
% 3.45/1.02  --sup_smt_interval                      50000
% 3.45/1.02  
% 3.45/1.02  ------ Superposition Simplification Setup
% 3.45/1.02  
% 3.45/1.02  --sup_indices_passive                   []
% 3.45/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.02  --sup_full_bw                           [BwDemod]
% 3.45/1.02  --sup_immed_triv                        [TrivRules]
% 3.45/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.02  --sup_immed_bw_main                     []
% 3.45/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.02  
% 3.45/1.02  ------ Combination Options
% 3.45/1.02  
% 3.45/1.02  --comb_res_mult                         3
% 3.45/1.02  --comb_sup_mult                         2
% 3.45/1.02  --comb_inst_mult                        10
% 3.45/1.02  
% 3.45/1.02  ------ Debug Options
% 3.45/1.02  
% 3.45/1.02  --dbg_backtrace                         false
% 3.45/1.02  --dbg_dump_prop_clauses                 false
% 3.45/1.02  --dbg_dump_prop_clauses_file            -
% 3.45/1.02  --dbg_out_stat                          false
% 3.45/1.02  
% 3.45/1.02  
% 3.45/1.02  
% 3.45/1.02  
% 3.45/1.02  ------ Proving...
% 3.45/1.02  
% 3.45/1.02  
% 3.45/1.02  % SZS status Theorem for theBenchmark.p
% 3.45/1.02  
% 3.45/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/1.02  
% 3.45/1.02  fof(f5,conjecture,(
% 3.45/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 3.45/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.02  
% 3.45/1.02  fof(f6,negated_conjecture,(
% 3.45/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 3.45/1.02    inference(negated_conjecture,[],[f5])).
% 3.45/1.02  
% 3.45/1.02  fof(f16,plain,(
% 3.45/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.45/1.02    inference(ennf_transformation,[],[f6])).
% 3.45/1.02  
% 3.45/1.02  fof(f17,plain,(
% 3.45/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f16])).
% 3.45/1.02  
% 3.45/1.02  fof(f20,plain,(
% 3.45/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.02    inference(nnf_transformation,[],[f17])).
% 3.45/1.02  
% 3.45/1.02  fof(f21,plain,(
% 3.45/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f20])).
% 3.45/1.02  
% 3.45/1.02  fof(f29,plain,(
% 3.45/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK7 = X5 & X5 = X6 & m1_subset_1(sK7,u1_struct_0(X4)))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f28,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK6 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f27,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f26,plain,(
% 3.45/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK4) = X0 & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f25,plain,(
% 3.45/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f24,plain,(
% 3.45/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) | ~r1_tmap_1(X0,X1,sK2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)) | r1_tmap_1(X0,X1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f23,plain,(
% 3.45/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) | ~r1_tmap_1(X0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)) | r1_tmap_1(X0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f22,plain,(
% 3.45/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & k1_tsep_1(sK0,X3,X4) = sK0 & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.45/1.02    introduced(choice_axiom,[])).
% 3.45/1.02  
% 3.45/1.02  fof(f30,plain,(
% 3.45/1.02    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & k1_tsep_1(sK0,sK3,sK4) = sK0 & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.45/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f29,f28,f27,f26,f25,f24,f23,f22])).
% 3.45/1.02  
% 3.45/1.02  fof(f57,plain,(
% 3.45/1.02    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f56,plain,(
% 3.45/1.02    sK5 = sK7),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f55,plain,(
% 3.45/1.02    sK5 = sK6),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f50,plain,(
% 3.45/1.02    m1_pre_topc(sK4,sK0)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f2,axiom,(
% 3.45/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.45/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.02  
% 3.45/1.02  fof(f10,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.02    inference(ennf_transformation,[],[f2])).
% 3.45/1.02  
% 3.45/1.02  fof(f11,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f10])).
% 3.45/1.02  
% 3.45/1.02  fof(f32,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(cnf_transformation,[],[f11])).
% 3.45/1.02  
% 3.45/1.02  fof(f45,plain,(
% 3.45/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f44,plain,(
% 3.45/1.02    v1_funct_1(sK2)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f41,plain,(
% 3.45/1.02    ~v2_struct_0(sK1)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f42,plain,(
% 3.45/1.02    v2_pre_topc(sK1)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f43,plain,(
% 3.45/1.02    l1_pre_topc(sK1)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f46,plain,(
% 3.45/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f1,axiom,(
% 3.45/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.45/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.02  
% 3.45/1.02  fof(f8,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.02    inference(ennf_transformation,[],[f1])).
% 3.45/1.02  
% 3.45/1.02  fof(f9,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f8])).
% 3.45/1.02  
% 3.45/1.02  fof(f31,plain,(
% 3.45/1.02    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(cnf_transformation,[],[f9])).
% 3.45/1.02  
% 3.45/1.02  fof(f38,plain,(
% 3.45/1.02    ~v2_struct_0(sK0)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f39,plain,(
% 3.45/1.02    v2_pre_topc(sK0)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f40,plain,(
% 3.45/1.02    l1_pre_topc(sK0)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f47,plain,(
% 3.45/1.02    ~v2_struct_0(sK3)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f48,plain,(
% 3.45/1.02    m1_pre_topc(sK3,sK0)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f49,plain,(
% 3.45/1.02    ~v2_struct_0(sK4)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f51,plain,(
% 3.45/1.02    k1_tsep_1(sK0,sK3,sK4) = sK0),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f3,axiom,(
% 3.45/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.45/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.02  
% 3.45/1.02  fof(f7,plain,(
% 3.45/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.45/1.02    inference(pure_predicate_removal,[],[f3])).
% 3.45/1.02  
% 3.45/1.02  fof(f12,plain,(
% 3.45/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.02    inference(ennf_transformation,[],[f7])).
% 3.45/1.02  
% 3.45/1.02  fof(f13,plain,(
% 3.45/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f12])).
% 3.45/1.02  
% 3.45/1.02  fof(f34,plain,(
% 3.45/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(cnf_transformation,[],[f13])).
% 3.45/1.02  
% 3.45/1.02  fof(f4,axiom,(
% 3.45/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) => ((X6 = X7 & X5 = X7) => (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))))))))))))),
% 3.45/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.02  
% 3.45/1.02  fof(f14,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | (X6 != X7 | X5 != X7)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.45/1.02    inference(ennf_transformation,[],[f4])).
% 3.45/1.02  
% 3.45/1.02  fof(f15,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f14])).
% 3.45/1.02  
% 3.45/1.02  fof(f18,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | (~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) & ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.02    inference(nnf_transformation,[],[f15])).
% 3.45/1.02  
% 3.45/1.02  fof(f19,plain,(
% 3.45/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) & ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.45/1.02    inference(flattening,[],[f18])).
% 3.45/1.02  
% 3.45/1.02  fof(f37,plain,(
% 3.45/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(cnf_transformation,[],[f19])).
% 3.45/1.02  
% 3.45/1.02  fof(f60,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(equality_resolution,[],[f37])).
% 3.45/1.02  
% 3.45/1.02  fof(f61,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(equality_resolution,[],[f60])).
% 3.45/1.02  
% 3.45/1.02  fof(f35,plain,(
% 3.45/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(cnf_transformation,[],[f19])).
% 3.45/1.02  
% 3.45/1.02  fof(f64,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(equality_resolution,[],[f35])).
% 3.45/1.02  
% 3.45/1.02  fof(f65,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(equality_resolution,[],[f64])).
% 3.45/1.02  
% 3.45/1.02  fof(f36,plain,(
% 3.45/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(cnf_transformation,[],[f19])).
% 3.45/1.02  
% 3.45/1.02  fof(f62,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(equality_resolution,[],[f36])).
% 3.45/1.02  
% 3.45/1.02  fof(f63,plain,(
% 3.45/1.02    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.45/1.02    inference(equality_resolution,[],[f62])).
% 3.45/1.02  
% 3.45/1.02  fof(f59,plain,(
% 3.45/1.02    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f54,plain,(
% 3.45/1.02    m1_subset_1(sK7,u1_struct_0(sK4))),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f52,plain,(
% 3.45/1.02    m1_subset_1(sK5,u1_struct_0(sK0))),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f53,plain,(
% 3.45/1.02    m1_subset_1(sK6,u1_struct_0(sK3))),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  fof(f58,plain,(
% 3.45/1.02    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 3.45/1.02    inference(cnf_transformation,[],[f30])).
% 3.45/1.02  
% 3.45/1.02  cnf(c_9,negated_conjecture,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 3.45/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_751,negated_conjecture,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1225,plain,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_10,negated_conjecture,
% 3.45/1.02      ( sK5 = sK7 ),
% 3.45/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_750,negated_conjecture,
% 3.45/1.02      ( sK5 = sK7 ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_11,negated_conjecture,
% 3.45/1.02      ( sK5 = sK6 ),
% 3.45/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_749,negated_conjecture,
% 3.45/1.02      ( sK5 = sK6 ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1247,plain,
% 3.45/1.02      ( sK6 = sK7 ),
% 3.45/1.02      inference(light_normalisation,[status(thm)],[c_749,c_750]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1287,plain,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 3.45/1.02      inference(light_normalisation,[status(thm)],[c_1225,c_750,c_1247]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_16,negated_conjecture,
% 3.45/1.02      ( m1_pre_topc(sK4,sK0) ),
% 3.45/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_744,negated_conjecture,
% 3.45/1.02      ( m1_pre_topc(sK4,sK0) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1229,plain,
% 3.45/1.02      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1,plain,
% 3.45/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.45/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X4)
% 3.45/1.02      | ~ m1_pre_topc(X3,X1)
% 3.45/1.02      | ~ m1_pre_topc(X1,X4)
% 3.45/1.02      | v2_struct_0(X4)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ v2_pre_topc(X4)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X4)
% 3.45/1.02      | ~ v1_funct_1(X0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.45/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_21,negated_conjecture,
% 3.45/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.45/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_269,plain,
% 3.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X1)
% 3.45/1.02      | ~ m1_pre_topc(X3,X4)
% 3.45/1.02      | ~ m1_pre_topc(X1,X4)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X4)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ v2_pre_topc(X4)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X4)
% 3.45/1.02      | ~ v1_funct_1(X0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.45/1.02      | sK2 != X0 ),
% 3.45/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_270,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X2,X0)
% 3.45/1.02      | ~ m1_pre_topc(X2,X3)
% 3.45/1.02      | ~ m1_pre_topc(X0,X3)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X3)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X3)
% 3.45/1.02      | ~ v1_funct_1(sK2)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
% 3.45/1.02      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.45/1.02      inference(unflattening,[status(thm)],[c_269]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_22,negated_conjecture,
% 3.45/1.02      ( v1_funct_1(sK2) ),
% 3.45/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_274,plain,
% 3.45/1.02      ( ~ l1_pre_topc(X3)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | ~ m1_pre_topc(X0,X3)
% 3.45/1.02      | ~ m1_pre_topc(X2,X3)
% 3.45/1.02      | ~ m1_pre_topc(X2,X0)
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
% 3.45/1.02      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_270,c_22]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_275,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X2,X0)
% 3.45/1.02      | ~ m1_pre_topc(X2,X3)
% 3.45/1.02      | ~ m1_pre_topc(X0,X3)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X3)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X3)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK2)
% 3.45/1.02      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_274]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_733,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 3.45/1.02      | ~ m1_pre_topc(X2_51,X0_51)
% 3.45/1.02      | ~ m1_pre_topc(X2_51,X3_51)
% 3.45/1.02      | ~ m1_pre_topc(X0_51,X3_51)
% 3.45/1.02      | v2_struct_0(X1_51)
% 3.45/1.02      | v2_struct_0(X3_51)
% 3.45/1.02      | ~ v2_pre_topc(X1_51)
% 3.45/1.02      | ~ v2_pre_topc(X3_51)
% 3.45/1.02      | ~ l1_pre_topc(X1_51)
% 3.45/1.02      | ~ l1_pre_topc(X3_51)
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK2) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_275]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1240,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK2)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X3_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(X3_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X3_51) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2154,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK1) = iProver_top
% 3.45/1.02      | v2_pre_topc(X2_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.02      | l1_pre_topc(X2_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.02      inference(equality_resolution,[status(thm)],[c_1240]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_25,negated_conjecture,
% 3.45/1.02      ( ~ v2_struct_0(sK1) ),
% 3.45/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_32,plain,
% 3.45/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_24,negated_conjecture,
% 3.45/1.02      ( v2_pre_topc(sK1) ),
% 3.45/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_33,plain,
% 3.45/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_23,negated_conjecture,
% 3.45/1.02      ( l1_pre_topc(sK1) ),
% 3.45/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_34,plain,
% 3.45/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_759,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1544,plain,
% 3.45/1.02      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.45/1.02      inference(instantiation,[status(thm)],[c_759]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1548,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 3.45/1.02      | ~ m1_pre_topc(X0_51,X1_51)
% 3.45/1.02      | ~ m1_pre_topc(X2_51,X0_51)
% 3.45/1.02      | ~ m1_pre_topc(X2_51,X1_51)
% 3.45/1.02      | v2_struct_0(X1_51)
% 3.45/1.02      | v2_struct_0(sK1)
% 3.45/1.02      | ~ v2_pre_topc(X1_51)
% 3.45/1.02      | ~ v2_pre_topc(sK1)
% 3.45/1.02      | ~ l1_pre_topc(X1_51)
% 3.45/1.02      | ~ l1_pre_topc(sK1)
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X2_51)) = k3_tmap_1(X1_51,sK1,X0_51,X2_51,sK2) ),
% 3.45/1.02      inference(instantiation,[status(thm)],[c_733]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1554,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK1) = iProver_top
% 3.45/1.02      | v2_pre_topc(X2_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.02      | l1_pre_topc(X2_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_1548]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2750,plain,
% 3.45/1.02      ( l1_pre_topc(X2_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | v2_pre_topc(X2_51) != iProver_top ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2154,c_32,c_33,c_34,c_1544,c_1554]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2751,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK1,X0_51,X1_51,sK2)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X2_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X2_51) != iProver_top ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_2750]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2765,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK0,X1_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top ),
% 3.45/1.02      inference(equality_resolution,[status(thm)],[c_2751]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_20,negated_conjecture,
% 3.45/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.45/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_37,plain,
% 3.45/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3048,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK2)
% 3.45/1.02      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK0,X1_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2765,c_37]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3061,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK0,sK4,sK2)
% 3.45/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_1229,c_3048]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_0,plain,
% 3.45/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.45/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X1)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ v1_funct_1(X0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.45/1.02      inference(cnf_transformation,[],[f31]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_320,plain,
% 3.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X1)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(X0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.45/1.02      | sK2 != X0 ),
% 3.45/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_321,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X2,X0)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | ~ v2_pre_topc(X0)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X0)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ v1_funct_1(sK2)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
% 3.45/1.02      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.45/1.02      inference(unflattening,[status(thm)],[c_320]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_325,plain,
% 3.45/1.02      ( ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X0)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | ~ m1_pre_topc(X2,X0)
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
% 3.45/1.02      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_321,c_22]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_326,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X2,X0)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X0)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK2,X2)
% 3.45/1.02      | u1_struct_0(X0) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_325]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_732,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 3.45/1.02      | ~ m1_pre_topc(X2_51,X0_51)
% 3.45/1.02      | v2_struct_0(X0_51)
% 3.45/1.02      | v2_struct_0(X1_51)
% 3.45/1.02      | ~ v2_pre_topc(X1_51)
% 3.45/1.02      | ~ v2_pre_topc(X0_51)
% 3.45/1.02      | ~ l1_pre_topc(X1_51)
% 3.45/1.02      | ~ l1_pre_topc(X0_51)
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_326]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1241,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK2,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK2,X2_51)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2086,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK1) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.02      inference(equality_resolution,[status(thm)],[c_1241]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1549,plain,
% 3.45/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 3.45/1.02      | ~ m1_pre_topc(X1_51,X0_51)
% 3.45/1.02      | v2_struct_0(X0_51)
% 3.45/1.02      | v2_struct_0(sK1)
% 3.45/1.02      | ~ v2_pre_topc(X0_51)
% 3.45/1.02      | ~ v2_pre_topc(sK1)
% 3.45/1.02      | ~ l1_pre_topc(X0_51)
% 3.45/1.02      | ~ l1_pre_topc(sK1)
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51) ),
% 3.45/1.02      inference(instantiation,[status(thm)],[c_732]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1550,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK1) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2638,plain,
% 3.45/1.02      ( l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2086,c_32,c_33,c_34,c_1544,c_1550]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2639,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 3.45/1.02      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),sK2,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,sK2,X1_51)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_2638]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2651,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X0_51,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(equality_resolution,[status(thm)],[c_2639]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_28,negated_conjecture,
% 3.45/1.02      ( ~ v2_struct_0(sK0) ),
% 3.45/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_29,plain,
% 3.45/1.02      ( v2_struct_0(sK0) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_27,negated_conjecture,
% 3.45/1.02      ( v2_pre_topc(sK0) ),
% 3.45/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_30,plain,
% 3.45/1.02      ( v2_pre_topc(sK0) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_26,negated_conjecture,
% 3.45/1.02      ( l1_pre_topc(sK0) ),
% 3.45/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_31,plain,
% 3.45/1.02      ( l1_pre_topc(sK0) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2864,plain,
% 3.45/1.02      ( m1_pre_topc(X0_51,sK0) != iProver_top
% 3.45/1.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2651,c_29,c_30,c_31,c_37]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2865,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK2,X0_51)
% 3.45/1.02      | m1_pre_topc(X0_51,sK0) != iProver_top ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_2864]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2872,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_1229,c_2865]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3115,plain,
% 3.45/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4)
% 3.45/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(light_normalisation,[status(thm)],[c_3061,c_2872]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_19,negated_conjecture,
% 3.45/1.02      ( ~ v2_struct_0(sK3) ),
% 3.45/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_38,plain,
% 3.45/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_18,negated_conjecture,
% 3.45/1.02      ( m1_pre_topc(sK3,sK0) ),
% 3.45/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_39,plain,
% 3.45/1.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_17,negated_conjecture,
% 3.45/1.02      ( ~ v2_struct_0(sK4) ),
% 3.45/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_40,plain,
% 3.45/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_41,plain,
% 3.45/1.02      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_15,negated_conjecture,
% 3.45/1.02      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 3.45/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_745,negated_conjecture,
% 3.45/1.02      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2,plain,
% 3.45/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.45/1.02      | ~ m1_pre_topc(X2,X1)
% 3.45/1.02      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | ~ l1_pre_topc(X1) ),
% 3.45/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_755,plain,
% 3.45/1.02      ( ~ m1_pre_topc(X0_51,X1_51)
% 3.45/1.02      | ~ m1_pre_topc(X2_51,X1_51)
% 3.45/1.02      | m1_pre_topc(k1_tsep_1(X1_51,X2_51,X0_51),X1_51)
% 3.45/1.02      | v2_struct_0(X0_51)
% 3.45/1.02      | v2_struct_0(X1_51)
% 3.45/1.02      | v2_struct_0(X2_51)
% 3.45/1.02      | ~ l1_pre_topc(X1_51) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1221,plain,
% 3.45/1.02      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(k1_tsep_1(X1_51,X2_51,X0_51),X1_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1655,plain,
% 3.45/1.02      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK0,sK0) = iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(sK3) = iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_struct_0(sK4) = iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_745,c_1221]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_4830,plain,
% 3.45/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK4,sK2) = k2_tmap_1(sK0,sK1,sK2,sK4) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_3115,c_29,c_30,c_31,c_38,c_39,c_40,c_41,c_1655]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_742,negated_conjecture,
% 3.45/1.02      ( m1_pre_topc(sK3,sK0) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1231,plain,
% 3.45/1.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3062,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK2)
% 3.45/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_1231,c_3048]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2873,plain,
% 3.45/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_1231,c_2865]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3102,plain,
% 3.45/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3)
% 3.45/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(light_normalisation,[status(thm)],[c_3062,c_2873]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3203,plain,
% 3.45/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK2) = k2_tmap_1(sK0,sK1,sK2,sK3) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_3102,c_29,c_30,c_31,c_38,c_39,c_40,c_41,c_1655]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_4,plain,
% 3.45/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 3.45/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X5)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 3.45/1.02      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 3.45/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(X4) ),
% 3.45/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_431,plain,
% 3.45/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 3.45/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X5)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 3.45/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(X4)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0)
% 3.45/1.02      | sK2 != X4 ),
% 3.45/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_432,plain,
% 3.45/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 3.45/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(sK2)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(unflattening,[status(thm)],[c_431]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_436,plain,
% 3.45/1.02      ( ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 3.45/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
% 3.45/1.02      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_432,c_22]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_437,plain,
% 3.45/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 3.45/1.02      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X3,sK2),X4)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_436]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_730,plain,
% 3.45/1.02      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X0_51,sK2),X0_52)
% 3.45/1.02      | ~ r1_tmap_1(X3_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X3_51,sK2),X0_52)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X2_51,X0_51,X3_51),X1_51,sK2,X0_52)
% 3.45/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 3.45/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 3.45/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)))
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)),u1_struct_0(X1_51))))
% 3.45/1.02      | ~ m1_pre_topc(X3_51,X2_51)
% 3.45/1.02      | ~ m1_pre_topc(X0_51,X2_51)
% 3.45/1.02      | v2_struct_0(X0_51)
% 3.45/1.02      | v2_struct_0(X1_51)
% 3.45/1.02      | v2_struct_0(X2_51)
% 3.45/1.02      | v2_struct_0(X3_51)
% 3.45/1.02      | ~ v2_pre_topc(X1_51)
% 3.45/1.02      | ~ v2_pre_topc(X2_51)
% 3.45/1.02      | ~ l1_pre_topc(X1_51)
% 3.45/1.02      | ~ l1_pre_topc(X2_51)
% 3.45/1.02      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_437]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1243,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
% 3.45/1.02      | r1_tmap_1(X2_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X2_51,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(X3_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X3_51,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) = iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X3_51,X1_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X3_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2539,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK3,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK3) = iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_struct_0(sK4) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_745,c_1243]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2540,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK3) = iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_struct_0(sK4) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(light_normalisation,[status(thm)],[c_2539,c_745]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2616,plain,
% 3.45/1.02      ( l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2540,c_29,c_30,c_31,c_38,c_39,c_40,c_41]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2617,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,X0_51,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_2616]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2633,plain,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.02      | v2_struct_0(sK1) = iProver_top
% 3.45/1.02      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.02      inference(equality_resolution,[status(thm)],[c_2617]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2735,plain,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2633,c_32,c_33,c_34,c_37]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_3206,plain,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.02      inference(demodulation,[status(thm)],[c_3203,c_2735]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_4833,plain,
% 3.45/1.02      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,sK1,sK2,X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.02      inference(demodulation,[status(thm)],[c_4830,c_3206]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_13964,plain,
% 3.45/1.02      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top
% 3.45/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_1287,c_4833]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_6,plain,
% 3.45/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,X4),X5)
% 3.45/1.02      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,X4,X5)
% 3.45/1.02      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
% 3.45/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(X4) ),
% 3.45/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_500,plain,
% 3.45/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,X4),X5)
% 3.45/1.02      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,X4,X5)
% 3.45/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(X4)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0)
% 3.45/1.02      | sK2 != X4 ),
% 3.45/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_501,plain,
% 3.45/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 3.45/1.02      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ v1_funct_1(sK2)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(unflattening,[status(thm)],[c_500]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_503,plain,
% 3.45/1.02      ( ~ l1_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.02      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 3.45/1.02      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_501,c_22]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_504,plain,
% 3.45/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,sK2),X4)
% 3.45/1.02      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X3),X1,sK2,X4)
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.02      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X3)))
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
% 3.45/1.02      | ~ m1_pre_topc(X3,X2)
% 3.45/1.02      | ~ m1_pre_topc(X0,X2)
% 3.45/1.02      | v2_struct_0(X0)
% 3.45/1.02      | v2_struct_0(X1)
% 3.45/1.02      | v2_struct_0(X2)
% 3.45/1.02      | v2_struct_0(X3)
% 3.45/1.02      | ~ v2_pre_topc(X1)
% 3.45/1.02      | ~ v2_pre_topc(X2)
% 3.45/1.02      | ~ l1_pre_topc(X1)
% 3.45/1.02      | ~ l1_pre_topc(X2)
% 3.45/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2,X0,X3)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(renaming,[status(thm)],[c_503]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_729,plain,
% 3.45/1.02      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X0_51,X3_51),X0_51,sK2),X0_52)
% 3.45/1.02      | ~ r1_tmap_1(k1_tsep_1(X2_51,X0_51,X3_51),X1_51,sK2,X0_52)
% 3.45/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 3.45/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 3.45/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)))
% 3.45/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)),u1_struct_0(X1_51))))
% 3.45/1.02      | ~ m1_pre_topc(X3_51,X2_51)
% 3.45/1.02      | ~ m1_pre_topc(X0_51,X2_51)
% 3.45/1.02      | v2_struct_0(X0_51)
% 3.45/1.02      | v2_struct_0(X1_51)
% 3.45/1.02      | v2_struct_0(X2_51)
% 3.45/1.02      | v2_struct_0(X3_51)
% 3.45/1.02      | ~ v2_pre_topc(X1_51)
% 3.45/1.02      | ~ v2_pre_topc(X2_51)
% 3.45/1.02      | ~ l1_pre_topc(X1_51)
% 3.45/1.02      | ~ l1_pre_topc(X2_51)
% 3.45/1.02      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X2_51,X0_51,X3_51)) != u1_struct_0(sK0) ),
% 3.45/1.02      inference(subtyping,[status(esa)],[c_504]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_1244,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
% 3.45/1.02      | r1_tmap_1(X2_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X2_51,sK2),X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(X3_51,X1_51) != iProver_top
% 3.45/1.02      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.02      | v2_struct_0(X3_51) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(X1_51) != iProver_top ),
% 3.45/1.02      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2361,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK3,sK2),X0_52) = iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK3) = iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_struct_0(sK4) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(superposition,[status(thm)],[c_745,c_1244]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2362,plain,
% 3.45/1.02      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.02      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | v2_struct_0(sK3) = iProver_top
% 3.45/1.02      | v2_struct_0(sK0) = iProver_top
% 3.45/1.02      | v2_struct_0(sK4) = iProver_top
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.02      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.02      inference(light_normalisation,[status(thm)],[c_2361,c_745]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2367,plain,
% 3.45/1.02      ( l1_pre_topc(X0_51) != iProver_top
% 3.45/1.02      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.02      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 3.45/1.02      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
% 3.45/1.02      | u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.02      | v2_pre_topc(X0_51) != iProver_top ),
% 3.45/1.02      inference(global_propositional_subsumption,
% 3.45/1.02                [status(thm)],
% 3.45/1.02                [c_2362,c_29,c_30,c_31,c_38,c_39,c_40,c_41]) ).
% 3.45/1.02  
% 3.45/1.02  cnf(c_2368,plain,
% 3.45/1.03      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.03      | r1_tmap_1(sK3,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK3,sK2),X0_52) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.03      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.03      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | l1_pre_topc(X0_51) != iProver_top ),
% 3.45/1.03      inference(renaming,[status(thm)],[c_2367]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2383,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.03      | v2_struct_0(sK1) = iProver_top
% 3.45/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.03      inference(equality_resolution,[status(thm)],[c_2368]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2508,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0_52) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.03      inference(global_propositional_subsumption,
% 3.45/1.03                [status(thm)],
% 3.45/1.03                [c_2383,c_32,c_33,c_34,c_37]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_3207,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_52) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.03      inference(demodulation,[status(thm)],[c_3203,c_2508]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_5,plain,
% 3.45/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 3.45/1.03      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 3.45/1.03      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
% 3.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.03      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 3.45/1.03      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.45/1.03      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.03      | ~ m1_pre_topc(X0,X2)
% 3.45/1.03      | ~ m1_pre_topc(X3,X2)
% 3.45/1.03      | v2_struct_0(X2)
% 3.45/1.03      | v2_struct_0(X1)
% 3.45/1.03      | v2_struct_0(X3)
% 3.45/1.03      | v2_struct_0(X0)
% 3.45/1.03      | ~ v2_pre_topc(X1)
% 3.45/1.03      | ~ v2_pre_topc(X2)
% 3.45/1.03      | ~ l1_pre_topc(X1)
% 3.45/1.03      | ~ l1_pre_topc(X2)
% 3.45/1.03      | ~ v1_funct_1(X4) ),
% 3.45/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_365,plain,
% 3.45/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
% 3.45/1.03      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,X4,X5)
% 3.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.03      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.45/1.03      | ~ m1_subset_1(X5,u1_struct_0(X0))
% 3.45/1.03      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.03      | ~ m1_pre_topc(X3,X2)
% 3.45/1.03      | ~ m1_pre_topc(X0,X2)
% 3.45/1.03      | v2_struct_0(X0)
% 3.45/1.03      | v2_struct_0(X1)
% 3.45/1.03      | v2_struct_0(X2)
% 3.45/1.03      | v2_struct_0(X3)
% 3.45/1.03      | ~ v2_pre_topc(X1)
% 3.45/1.03      | ~ v2_pre_topc(X2)
% 3.45/1.03      | ~ l1_pre_topc(X1)
% 3.45/1.03      | ~ l1_pre_topc(X2)
% 3.45/1.03      | ~ v1_funct_1(X4)
% 3.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.03      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0)
% 3.45/1.03      | sK2 != X4 ),
% 3.45/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_366,plain,
% 3.45/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
% 3.45/1.03      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.03      | ~ m1_pre_topc(X3,X2)
% 3.45/1.03      | ~ m1_pre_topc(X0,X2)
% 3.45/1.03      | v2_struct_0(X0)
% 3.45/1.03      | v2_struct_0(X1)
% 3.45/1.03      | v2_struct_0(X2)
% 3.45/1.03      | v2_struct_0(X3)
% 3.45/1.03      | ~ v2_pre_topc(X1)
% 3.45/1.03      | ~ v2_pre_topc(X2)
% 3.45/1.03      | ~ l1_pre_topc(X1)
% 3.45/1.03      | ~ l1_pre_topc(X2)
% 3.45/1.03      | ~ v1_funct_1(sK2)
% 3.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.03      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
% 3.45/1.03      inference(unflattening,[status(thm)],[c_365]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_370,plain,
% 3.45/1.03      ( ~ l1_pre_topc(X2)
% 3.45/1.03      | ~ l1_pre_topc(X1)
% 3.45/1.03      | ~ v2_pre_topc(X2)
% 3.45/1.03      | ~ v2_pre_topc(X1)
% 3.45/1.03      | v2_struct_0(X3)
% 3.45/1.03      | v2_struct_0(X2)
% 3.45/1.03      | v2_struct_0(X1)
% 3.45/1.03      | v2_struct_0(X0)
% 3.45/1.03      | ~ m1_pre_topc(X0,X2)
% 3.45/1.03      | ~ m1_pre_topc(X3,X2)
% 3.45/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.03      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
% 3.45/1.03      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
% 3.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.03      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
% 3.45/1.03      inference(global_propositional_subsumption,
% 3.45/1.03                [status(thm)],
% 3.45/1.03                [c_366,c_22]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_371,plain,
% 3.45/1.03      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,sK2),X4)
% 3.45/1.03      | ~ r1_tmap_1(k1_tsep_1(X2,X3,X0),X1,sK2,X4)
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.45/1.03      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)))
% 3.45/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
% 3.45/1.03      | ~ m1_pre_topc(X3,X2)
% 3.45/1.03      | ~ m1_pre_topc(X0,X2)
% 3.45/1.03      | v2_struct_0(X0)
% 3.45/1.03      | v2_struct_0(X1)
% 3.45/1.03      | v2_struct_0(X2)
% 3.45/1.03      | v2_struct_0(X3)
% 3.45/1.03      | ~ v2_pre_topc(X1)
% 3.45/1.03      | ~ v2_pre_topc(X2)
% 3.45/1.03      | ~ l1_pre_topc(X1)
% 3.45/1.03      | ~ l1_pre_topc(X2)
% 3.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.45/1.03      | u1_struct_0(k1_tsep_1(X2,X3,X0)) != u1_struct_0(sK0) ),
% 3.45/1.03      inference(renaming,[status(thm)],[c_370]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_731,plain,
% 3.45/1.03      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,k1_tsep_1(X2_51,X3_51,X0_51),X0_51,sK2),X0_52)
% 3.45/1.03      | ~ r1_tmap_1(k1_tsep_1(X2_51,X3_51,X0_51),X1_51,sK2,X0_52)
% 3.45/1.03      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 3.45/1.03      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 3.45/1.03      | ~ m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)))
% 3.45/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)),u1_struct_0(X1_51))))
% 3.45/1.03      | ~ m1_pre_topc(X3_51,X2_51)
% 3.45/1.03      | ~ m1_pre_topc(X0_51,X2_51)
% 3.45/1.03      | v2_struct_0(X0_51)
% 3.45/1.03      | v2_struct_0(X1_51)
% 3.45/1.03      | v2_struct_0(X2_51)
% 3.45/1.03      | v2_struct_0(X3_51)
% 3.45/1.03      | ~ v2_pre_topc(X1_51)
% 3.45/1.03      | ~ v2_pre_topc(X2_51)
% 3.45/1.03      | ~ l1_pre_topc(X1_51)
% 3.45/1.03      | ~ l1_pre_topc(X2_51)
% 3.45/1.03      | u1_struct_0(X1_51) != u1_struct_0(sK1)
% 3.45/1.03      | u1_struct_0(k1_tsep_1(X2_51,X3_51,X0_51)) != u1_struct_0(sK0) ),
% 3.45/1.03      inference(subtyping,[status(esa)],[c_371]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1242,plain,
% 3.45/1.03      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.03      | u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)) != u1_struct_0(sK0)
% 3.45/1.03      | r1_tmap_1(X3_51,X0_51,k3_tmap_1(X1_51,X0_51,k1_tsep_1(X1_51,X2_51,X3_51),X3_51,sK2),X0_52) = iProver_top
% 3.45/1.03      | r1_tmap_1(k1_tsep_1(X1_51,X2_51,X3_51),X0_51,sK2,X0_52) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(X2_51)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(X3_51)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51))) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_51,X2_51,X3_51)),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.03      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 3.45/1.03      | m1_pre_topc(X3_51,X1_51) != iProver_top
% 3.45/1.03      | v2_struct_0(X1_51) = iProver_top
% 3.45/1.03      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.03      | v2_struct_0(X3_51) = iProver_top
% 3.45/1.03      | v2_struct_0(X2_51) = iProver_top
% 3.45/1.03      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | v2_pre_topc(X1_51) != iProver_top
% 3.45/1.03      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | l1_pre_topc(X1_51) != iProver_top ),
% 3.45/1.03      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2177,plain,
% 3.45/1.03      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.03      | r1_tmap_1(k1_tsep_1(sK0,sK3,sK4),X0_51,sK2,X0_52) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,k1_tsep_1(sK0,sK3,sK4),sK4,sK2),X0_52) = iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.03      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.03      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.03      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.03      | v2_struct_0(sK3) = iProver_top
% 3.45/1.03      | v2_struct_0(sK0) = iProver_top
% 3.45/1.03      | v2_struct_0(sK4) = iProver_top
% 3.45/1.03      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.03      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.03      inference(superposition,[status(thm)],[c_745,c_1242]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2178,plain,
% 3.45/1.03      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.03      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.03      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.45/1.03      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.45/1.03      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.03      | v2_struct_0(sK3) = iProver_top
% 3.45/1.03      | v2_struct_0(sK0) = iProver_top
% 3.45/1.03      | v2_struct_0(sK4) = iProver_top
% 3.45/1.03      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | v2_pre_topc(sK0) != iProver_top
% 3.45/1.03      | l1_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | l1_pre_topc(sK0) != iProver_top ),
% 3.45/1.03      inference(light_normalisation,[status(thm)],[c_2177,c_745]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2237,plain,
% 3.45/1.03      ( l1_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 3.45/1.03      | u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.03      | v2_pre_topc(X0_51) != iProver_top ),
% 3.45/1.03      inference(global_propositional_subsumption,
% 3.45/1.03                [status(thm)],
% 3.45/1.03                [c_2178,c_29,c_30,c_31,c_38,c_39,c_40,c_41]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2238,plain,
% 3.45/1.03      ( u1_struct_0(X0_51) != u1_struct_0(sK1)
% 3.45/1.03      | r1_tmap_1(sK0,X0_51,sK2,X0_52) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,X0_51,k3_tmap_1(sK0,X0_51,sK0,sK4,sK2),X0_52) = iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_51)))) != iProver_top
% 3.45/1.03      | v2_struct_0(X0_51) = iProver_top
% 3.45/1.03      | v2_pre_topc(X0_51) != iProver_top
% 3.45/1.03      | l1_pre_topc(X0_51) != iProver_top ),
% 3.45/1.03      inference(renaming,[status(thm)],[c_2237]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2253,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.45/1.03      | v2_struct_0(sK1) = iProver_top
% 3.45/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.45/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.45/1.03      inference(equality_resolution,[status(thm)],[c_2238]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_2258,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0_52) = iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.03      inference(global_propositional_subsumption,
% 3.45/1.03                [status(thm)],
% 3.45/1.03                [c_2253,c_32,c_33,c_34,c_37]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_4834,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,X0_52) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_52) = iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.03      inference(demodulation,[status(thm)],[c_4830,c_2258]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_7,negated_conjecture,
% 3.45/1.03      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.45/1.03      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.45/1.03      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.45/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_753,negated_conjecture,
% 3.45/1.03      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.45/1.03      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.45/1.03      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.45/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1223,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 3.45/1.03      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1292,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 3.45/1.03      inference(light_normalisation,[status(thm)],[c_1223,c_750,c_1247]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_8744,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.03      inference(superposition,[status(thm)],[c_4834,c_1292]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_12,negated_conjecture,
% 3.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 3.45/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_44,plain,
% 3.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 3.45/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_14,negated_conjecture,
% 3.45/1.03      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 3.45/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_746,negated_conjecture,
% 3.45/1.03      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 3.45/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1228,plain,
% 3.45/1.03      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 3.45/1.03      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1275,plain,
% 3.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
% 3.45/1.03      inference(light_normalisation,[status(thm)],[c_1228,c_750]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_13,negated_conjecture,
% 3.45/1.03      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.45/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_747,negated_conjecture,
% 3.45/1.03      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.45/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1227,plain,
% 3.45/1.03      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.45/1.03      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1272,plain,
% 3.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 3.45/1.03      inference(light_normalisation,[status(thm)],[c_1227,c_1247]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_8747,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top ),
% 3.45/1.03      inference(global_propositional_subsumption,
% 3.45/1.03                [status(thm)],
% 3.45/1.03                [c_8744,c_44,c_1275,c_1272]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_8748,plain,
% 3.45/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 3.45/1.03      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
% 3.45/1.03      inference(renaming,[status(thm)],[c_8747]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_8754,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 3.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 3.45/1.03      inference(superposition,[status(thm)],[c_3207,c_8748]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_8,negated_conjecture,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.45/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_752,negated_conjecture,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.45/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1224,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 3.45/1.03      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(c_1282,plain,
% 3.45/1.03      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 3.45/1.03      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 3.45/1.03      inference(light_normalisation,[status(thm)],[c_1224,c_750]) ).
% 3.45/1.03  
% 3.45/1.03  cnf(contradiction,plain,
% 3.45/1.03      ( $false ),
% 3.45/1.03      inference(minisat,
% 3.45/1.03                [status(thm)],
% 3.45/1.03                [c_13964,c_8754,c_1272,c_1275,c_1282,c_44]) ).
% 3.45/1.03  
% 3.45/1.03  
% 3.45/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.03  
% 3.45/1.03  ------                               Statistics
% 3.45/1.03  
% 3.45/1.03  ------ General
% 3.45/1.03  
% 3.45/1.03  abstr_ref_over_cycles:                  0
% 3.45/1.03  abstr_ref_under_cycles:                 0
% 3.45/1.03  gc_basic_clause_elim:                   0
% 3.45/1.03  forced_gc_time:                         0
% 3.45/1.03  parsing_time:                           0.009
% 3.45/1.03  unif_index_cands_time:                  0.
% 3.45/1.03  unif_index_add_time:                    0.
% 3.45/1.03  orderings_time:                         0.
% 3.45/1.03  out_proof_time:                         0.02
% 3.45/1.03  total_time:                             0.503
% 3.45/1.03  num_of_symbols:                         55
% 3.45/1.03  num_of_terms:                           7483
% 3.45/1.03  
% 3.45/1.03  ------ Preprocessing
% 3.45/1.03  
% 3.45/1.03  num_of_splits:                          0
% 3.45/1.03  num_of_split_atoms:                     0
% 3.45/1.03  num_of_reused_defs:                     0
% 3.45/1.03  num_eq_ax_congr_red:                    11
% 3.45/1.03  num_of_sem_filtered_clauses:            1
% 3.45/1.03  num_of_subtypes:                        4
% 3.45/1.03  monotx_restored_types:                  0
% 3.45/1.03  sat_num_of_epr_types:                   0
% 3.45/1.03  sat_num_of_non_cyclic_types:            0
% 3.45/1.03  sat_guarded_non_collapsed_types:        0
% 3.45/1.03  num_pure_diseq_elim:                    0
% 3.45/1.03  simp_replaced_by:                       0
% 3.45/1.03  res_preprocessed:                       151
% 3.45/1.03  prep_upred:                             0
% 3.45/1.03  prep_unflattend:                        5
% 3.45/1.03  smt_new_axioms:                         0
% 3.45/1.03  pred_elim_cands:                        6
% 3.45/1.03  pred_elim:                              2
% 3.45/1.03  pred_elim_cl:                           2
% 3.45/1.03  pred_elim_cycles:                       4
% 3.45/1.03  merged_defs:                            0
% 3.45/1.03  merged_defs_ncl:                        0
% 3.45/1.03  bin_hyper_res:                          0
% 3.45/1.03  prep_cycles:                            4
% 3.45/1.03  pred_elim_time:                         0.014
% 3.45/1.03  splitting_time:                         0.
% 3.45/1.03  sem_filter_time:                        0.
% 3.45/1.03  monotx_time:                            0.
% 3.45/1.03  subtype_inf_time:                       0.001
% 3.45/1.03  
% 3.45/1.03  ------ Problem properties
% 3.45/1.03  
% 3.45/1.03  clauses:                                27
% 3.45/1.03  conjectures:                            20
% 3.45/1.03  epr:                                    12
% 3.45/1.03  horn:                                   18
% 3.45/1.03  ground:                                 20
% 3.45/1.03  unary:                                  17
% 3.45/1.03  binary:                                 2
% 3.45/1.03  lits:                                   117
% 3.45/1.03  lits_eq:                                15
% 3.45/1.03  fd_pure:                                0
% 3.45/1.03  fd_pseudo:                              0
% 3.45/1.03  fd_cond:                                0
% 3.45/1.03  fd_pseudo_cond:                         0
% 3.45/1.03  ac_symbols:                             0
% 3.45/1.03  
% 3.45/1.03  ------ Propositional Solver
% 3.45/1.03  
% 3.45/1.03  prop_solver_calls:                      30
% 3.45/1.03  prop_fast_solver_calls:                 2435
% 3.45/1.03  smt_solver_calls:                       0
% 3.45/1.03  smt_fast_solver_calls:                  0
% 3.45/1.03  prop_num_of_clauses:                    4007
% 3.45/1.03  prop_preprocess_simplified:             7995
% 3.45/1.03  prop_fo_subsumed:                       219
% 3.45/1.03  prop_solver_time:                       0.
% 3.45/1.03  smt_solver_time:                        0.
% 3.45/1.03  smt_fast_solver_time:                   0.
% 3.45/1.03  prop_fast_solver_time:                  0.
% 3.45/1.03  prop_unsat_core_time:                   0.
% 3.45/1.03  
% 3.45/1.03  ------ QBF
% 3.45/1.03  
% 3.45/1.03  qbf_q_res:                              0
% 3.45/1.03  qbf_num_tautologies:                    0
% 3.45/1.03  qbf_prep_cycles:                        0
% 3.45/1.03  
% 3.45/1.03  ------ BMC1
% 3.45/1.03  
% 3.45/1.03  bmc1_current_bound:                     -1
% 3.45/1.03  bmc1_last_solved_bound:                 -1
% 3.45/1.03  bmc1_unsat_core_size:                   -1
% 3.45/1.03  bmc1_unsat_core_parents_size:           -1
% 3.45/1.03  bmc1_merge_next_fun:                    0
% 3.45/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.03  
% 3.45/1.03  ------ Instantiation
% 3.45/1.03  
% 3.45/1.03  inst_num_of_clauses:                    1197
% 3.45/1.03  inst_num_in_passive:                    241
% 3.45/1.03  inst_num_in_active:                     827
% 3.45/1.03  inst_num_in_unprocessed:                129
% 3.45/1.03  inst_num_of_loops:                      880
% 3.45/1.03  inst_num_of_learning_restarts:          0
% 3.45/1.03  inst_num_moves_active_passive:          44
% 3.45/1.03  inst_lit_activity:                      0
% 3.45/1.03  inst_lit_activity_moves:                0
% 3.45/1.03  inst_num_tautologies:                   0
% 3.45/1.03  inst_num_prop_implied:                  0
% 3.45/1.03  inst_num_existing_simplified:           0
% 3.45/1.03  inst_num_eq_res_simplified:             0
% 3.45/1.03  inst_num_child_elim:                    0
% 3.45/1.03  inst_num_of_dismatching_blockings:      1439
% 3.45/1.03  inst_num_of_non_proper_insts:           2155
% 3.45/1.03  inst_num_of_duplicates:                 0
% 3.45/1.03  inst_inst_num_from_inst_to_res:         0
% 3.45/1.03  inst_dismatching_checking_time:         0.
% 3.45/1.03  
% 3.45/1.03  ------ Resolution
% 3.45/1.03  
% 3.45/1.03  res_num_of_clauses:                     0
% 3.45/1.03  res_num_in_passive:                     0
% 3.45/1.03  res_num_in_active:                      0
% 3.45/1.03  res_num_of_loops:                       155
% 3.45/1.03  res_forward_subset_subsumed:            333
% 3.45/1.03  res_backward_subset_subsumed:           2
% 3.45/1.03  res_forward_subsumed:                   0
% 3.45/1.03  res_backward_subsumed:                  0
% 3.45/1.03  res_forward_subsumption_resolution:     0
% 3.45/1.03  res_backward_subsumption_resolution:    0
% 3.45/1.03  res_clause_to_clause_subsumption:       2322
% 3.45/1.03  res_orphan_elimination:                 0
% 3.45/1.03  res_tautology_del:                      391
% 3.45/1.03  res_num_eq_res_simplified:              0
% 3.45/1.03  res_num_sel_changes:                    0
% 3.45/1.03  res_moves_from_active_to_pass:          0
% 3.45/1.03  
% 3.45/1.03  ------ Superposition
% 3.45/1.03  
% 3.45/1.03  sup_time_total:                         0.
% 3.45/1.03  sup_time_generating:                    0.
% 3.45/1.03  sup_time_sim_full:                      0.
% 3.45/1.03  sup_time_sim_immed:                     0.
% 3.45/1.03  
% 3.45/1.03  sup_num_of_clauses:                     210
% 3.45/1.03  sup_num_in_active:                      162
% 3.45/1.03  sup_num_in_passive:                     48
% 3.45/1.03  sup_num_of_loops:                       174
% 3.45/1.03  sup_fw_superposition:                   198
% 3.45/1.03  sup_bw_superposition:                   11
% 3.45/1.03  sup_immediate_simplified:               35
% 3.45/1.03  sup_given_eliminated:                   0
% 3.45/1.03  comparisons_done:                       0
% 3.45/1.03  comparisons_avoided:                    0
% 3.45/1.03  
% 3.45/1.03  ------ Simplifications
% 3.45/1.03  
% 3.45/1.03  
% 3.45/1.03  sim_fw_subset_subsumed:                 1
% 3.45/1.03  sim_bw_subset_subsumed:                 10
% 3.45/1.03  sim_fw_subsumed:                        0
% 3.45/1.03  sim_bw_subsumed:                        0
% 3.45/1.03  sim_fw_subsumption_res:                 0
% 3.45/1.03  sim_bw_subsumption_res:                 0
% 3.45/1.03  sim_tautology_del:                      5
% 3.45/1.03  sim_eq_tautology_del:                   20
% 3.45/1.03  sim_eq_res_simp:                        0
% 3.45/1.03  sim_fw_demodulated:                     0
% 3.45/1.03  sim_bw_demodulated:                     4
% 3.45/1.03  sim_light_normalised:                   40
% 3.45/1.03  sim_joinable_taut:                      0
% 3.45/1.03  sim_joinable_simp:                      0
% 3.45/1.03  sim_ac_normalised:                      0
% 3.45/1.03  sim_smt_subsumption:                    0
% 3.45/1.03  
%------------------------------------------------------------------------------
