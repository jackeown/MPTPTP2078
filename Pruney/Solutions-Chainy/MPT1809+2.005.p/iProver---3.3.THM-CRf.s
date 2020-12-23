%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:16 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  233 (8587 expanded)
%              Number of clauses        :  153 (1411 expanded)
%              Number of leaves         :   17 (3904 expanded)
%              Depth                    :   28
%              Number of atoms          : 1849 (182690 expanded)
%              Number of equality atoms :  662 (29138 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
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
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( ( X5 = X7
                                      & X5 = X6 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                    <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f82,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f80,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f73,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_413,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1069,plain,
    ( m1_pre_topc(X0_53,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_398,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1081,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X3_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X1_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X3_53)) = k3_tmap_1(X2_53,X1_53,X0_53,X3_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1062,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_2780,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK0,X0_53,sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1062])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_42,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2996,plain,
    ( v2_pre_topc(X1_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK0,X0_53,sK2)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2780,c_38,c_39,c_40,c_41,c_42])).

cnf(c_2997,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK0,X0_53,sK2)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2996])).

cnf(c_3011,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK1,sK0,X0_53,sK2)
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | m1_pre_topc(sK0,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_2997])).

cnf(c_3670,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_3011])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1061,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_2424,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1061])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_35,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_36,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2849,plain,
    ( m1_pre_topc(X0_53,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2424,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42])).

cnf(c_2850,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53)
    | m1_pre_topc(X0_53,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2849])).

cnf(c_2859,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_2850])).

cnf(c_58,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1545,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_53,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_1547,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_3054,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2859,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_58,c_1547])).

cnf(c_3676,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK2) = k2_tmap_1(sK0,sK1,sK2,sK0)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3670,c_3054])).

cnf(c_57,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_59,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_3794,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK2) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3676,c_35,c_36,c_37,c_59])).

cnf(c_12,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_412,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54))
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1070,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_3797,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_1070])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3849,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_59])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_419,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1063,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
    | l1_struct_0(X2_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_423,plain,
    ( ~ r2_funct_2(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X1_54,X0_55,X1_55)
    | ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | X0_54 = X1_54 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1059,plain,
    ( X0_54 = X1_54
    | r2_funct_2(X0_55,X1_55,X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(X1_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_1976,plain,
    ( sK2 = X0_54
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1059])).

cnf(c_2342,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sK2 = X0_54
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1976,c_41,c_42])).

cnf(c_2343,plain,
    ( sK2 = X0_54
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2342])).

cnf(c_2578,plain,
    ( k2_tmap_1(X0_53,sK1,X0_54,sK0) = sK2
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_2343])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_82,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_84,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_422,plain,
    ( ~ l1_pre_topc(X0_53)
    | l1_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1924,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_1925,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_3129,plain,
    ( k2_tmap_1(X0_53,sK1,X0_54,sK0) = sK2
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2578,c_37,c_40,c_84,c_1925])).

cnf(c_3854,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3849,c_3129])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1518,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_53)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0_53))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1519,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0_53)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_1521,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK0)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_418,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1523,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0_53),u1_struct_0(X0_53),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_53)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1524,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0_53),u1_struct_0(X0_53),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_1526,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_2708,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_3857,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3854,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_59,c_84,c_1521,c_1526,c_1925,c_2708,c_3797])).

cnf(c_21,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_403,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_414,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
    | ~ r1_tmap_1(k1_tsep_1(X2_53,X0_53,X3_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X0_53,X3_53)),X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_subset_1(X1_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X0_53,X3_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1068,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
    | r1_tmap_1(k1_tsep_1(X2_53,X0_53,X3_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X0_53,X3_53)),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X3_53,X2_53) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X3_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X0_53,X3_53))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_3426,plain,
    ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_1068])).

cnf(c_3446,plain,
    ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3426,c_403])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_47,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3469,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3446,c_35,c_36,c_37,c_44,c_45,c_46,c_47])).

cnf(c_3470,plain,
    ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3469])).

cnf(c_3875,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_54) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_3470])).

cnf(c_4364,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_54) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_38,c_39,c_40,c_41,c_42,c_43])).

cnf(c_4365,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_54) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4364])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_415,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
    | ~ r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_subset_1(X1_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1067,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
    | r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X3_53,X2_53) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X3_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_3272,plain,
    ( r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_1067])).

cnf(c_3292,plain,
    ( r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3272,c_403])).

cnf(c_3315,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3292,c_35,c_36,c_37,c_44,c_45,c_46,c_47])).

cnf(c_3316,plain,
    ( r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3315])).

cnf(c_3876,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_54) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_3316])).

cnf(c_4475,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3876,c_38,c_39,c_40,c_41,c_42,c_43])).

cnf(c_4476,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4475])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_411,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1071,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_16,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_408,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_17,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_407,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1092,plain,
    ( sK6 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_407,c_408])).

cnf(c_1157,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1071,c_408,c_1092])).

cnf(c_4486,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4476,c_1157])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_405,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1075,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_1119,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1075,c_1092])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_404,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1076,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1122,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1076,c_408])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_410,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1072,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_1139,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1072,c_408])).

cnf(c_8,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
    | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_416,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
    | ~ r1_tmap_1(X3_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X3_53),X1_54)
    | r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_subset_1(X1_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1066,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) != iProver_top
    | r1_tmap_1(X3_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X3_53),X1_54) != iProver_top
    | r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X3_53,X2_53) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X3_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_3206,plain,
    ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_1066])).

cnf(c_3208,plain,
    ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3206,c_403])).

cnf(c_3579,plain,
    ( l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
    | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3208,c_35,c_36,c_37,c_44,c_45,c_46,c_47])).

cnf(c_3580,plain,
    ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
    | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
    | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3579])).

cnf(c_3597,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_3580])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_409,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1073,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_1144,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1073,c_408,c_1092])).

cnf(c_3600,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_38,c_39,c_40,c_41,c_42,c_43,c_50,c_1119,c_1144,c_1122])).

cnf(c_3601,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_3600])).

cnf(c_3862,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3857,c_3601])).

cnf(c_4513,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4486,c_50,c_1119,c_1122,c_3862])).

cnf(c_4519,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4365,c_4513])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4519,c_3862,c_1122,c_1119,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:52:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.63/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/1.00  
% 2.63/1.00  ------  iProver source info
% 2.63/1.00  
% 2.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/1.00  git: non_committed_changes: false
% 2.63/1.00  git: last_make_outside_of_git: false
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     num_symb
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       true
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  ------ Parsing...
% 2.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/1.00  ------ Proving...
% 2.63/1.00  ------ Problem Properties 
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  clauses                                 35
% 2.63/1.00  conjectures                             22
% 2.63/1.00  EPR                                     15
% 2.63/1.00  Horn                                    27
% 2.63/1.00  unary                                   19
% 2.63/1.00  binary                                  4
% 2.63/1.00  lits                                    154
% 2.63/1.00  lits eq                                 6
% 2.63/1.00  fd_pure                                 0
% 2.63/1.00  fd_pseudo                               0
% 2.63/1.00  fd_cond                                 0
% 2.63/1.00  fd_pseudo_cond                          1
% 2.63/1.00  AC symbols                              0
% 2.63/1.00  
% 2.63/1.00  ------ Schedule dynamic 5 is on 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  Current options:
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     none
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       false
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ Proving...
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS status Theorem for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  fof(f7,axiom,(
% 2.63/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f22,plain,(
% 2.63/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f7])).
% 2.63/1.00  
% 2.63/1.00  fof(f52,plain,(
% 2.63/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f22])).
% 2.63/1.00  
% 2.63/1.00  fof(f9,conjecture,(
% 2.63/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f10,negated_conjecture,(
% 2.63/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.63/1.00    inference(negated_conjecture,[],[f9])).
% 2.63/1.00  
% 2.63/1.00  fof(f25,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f10])).
% 2.63/1.00  
% 2.63/1.00  fof(f26,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f25])).
% 2.63/1.00  
% 2.63/1.00  fof(f30,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.63/1.00    inference(nnf_transformation,[],[f26])).
% 2.63/1.00  
% 2.63/1.00  fof(f31,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f30])).
% 2.63/1.00  
% 2.63/1.00  fof(f39,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK7 = X5 & X5 = X6 & m1_subset_1(sK7,u1_struct_0(X4)))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f38,plain,(
% 2.63/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK6 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f37,plain,(
% 2.63/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f36,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK4) = X0 & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f35,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f34,plain,(
% 2.63/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) | ~r1_tmap_1(X0,X1,sK2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)) | r1_tmap_1(X0,X1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f33,plain,(
% 2.63/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) | ~r1_tmap_1(X0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)) | r1_tmap_1(X0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f32,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & k1_tsep_1(sK0,X3,X4) = sK0 & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f40,plain,(
% 2.63/1.00    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & k1_tsep_1(sK0,sK3,sK4) = sK0 & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).
% 2.63/1.00  
% 2.63/1.00  fof(f62,plain,(
% 2.63/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f4,axiom,(
% 2.63/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f16,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f4])).
% 2.63/1.00  
% 2.63/1.00  fof(f17,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f16])).
% 2.63/1.00  
% 2.63/1.00  fof(f45,plain,(
% 2.63/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f17])).
% 2.63/1.00  
% 2.63/1.00  fof(f57,plain,(
% 2.63/1.00    ~v2_struct_0(sK1)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f58,plain,(
% 2.63/1.00    v2_pre_topc(sK1)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f59,plain,(
% 2.63/1.00    l1_pre_topc(sK1)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f60,plain,(
% 2.63/1.00    v1_funct_1(sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f61,plain,(
% 2.63/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f3,axiom,(
% 2.63/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f14,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f3])).
% 2.63/1.00  
% 2.63/1.00  fof(f15,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f14])).
% 2.63/1.00  
% 2.63/1.00  fof(f44,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f15])).
% 2.63/1.00  
% 2.63/1.00  fof(f54,plain,(
% 2.63/1.00    ~v2_struct_0(sK0)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f55,plain,(
% 2.63/1.00    v2_pre_topc(sK0)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f56,plain,(
% 2.63/1.00    l1_pre_topc(sK0)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f8,axiom,(
% 2.63/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f23,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f8])).
% 2.63/1.00  
% 2.63/1.00  fof(f24,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f23])).
% 2.63/1.00  
% 2.63/1.00  fof(f53,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f24])).
% 2.63/1.00  
% 2.63/1.00  fof(f5,axiom,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f18,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f5])).
% 2.63/1.00  
% 2.63/1.00  fof(f19,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f18])).
% 2.63/1.00  
% 2.63/1.00  fof(f48,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f19])).
% 2.63/1.00  
% 2.63/1.00  fof(f1,axiom,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f11,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.63/1.00    inference(ennf_transformation,[],[f1])).
% 2.63/1.00  
% 2.63/1.00  fof(f12,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(flattening,[],[f11])).
% 2.63/1.00  
% 2.63/1.00  fof(f27,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(nnf_transformation,[],[f12])).
% 2.63/1.00  
% 2.63/1.00  fof(f41,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f27])).
% 2.63/1.00  
% 2.63/1.00  fof(f2,axiom,(
% 2.63/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f13,plain,(
% 2.63/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f2])).
% 2.63/1.00  
% 2.63/1.00  fof(f43,plain,(
% 2.63/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f13])).
% 2.63/1.00  
% 2.63/1.00  fof(f46,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f19])).
% 2.63/1.00  
% 2.63/1.00  fof(f47,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f19])).
% 2.63/1.00  
% 2.63/1.00  fof(f67,plain,(
% 2.63/1.00    k1_tsep_1(sK0,sK3,sK4) = sK0),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f6,axiom,(
% 2.63/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 2.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f20,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f6])).
% 2.63/1.00  
% 2.63/1.00  fof(f21,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f20])).
% 2.63/1.00  
% 2.63/1.00  fof(f28,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(nnf_transformation,[],[f21])).
% 2.63/1.00  
% 2.63/1.00  fof(f29,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f28])).
% 2.63/1.00  
% 2.63/1.00  fof(f49,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f29])).
% 2.63/1.00  
% 2.63/1.00  fof(f81,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(equality_resolution,[],[f49])).
% 2.63/1.00  
% 2.63/1.00  fof(f82,plain,(
% 2.63/1.00    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(equality_resolution,[],[f81])).
% 2.63/1.00  
% 2.63/1.00  fof(f63,plain,(
% 2.63/1.00    ~v2_struct_0(sK3)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f64,plain,(
% 2.63/1.00    m1_pre_topc(sK3,sK0)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f65,plain,(
% 2.63/1.00    ~v2_struct_0(sK4)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f66,plain,(
% 2.63/1.00    m1_pre_topc(sK4,sK0)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f50,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f29])).
% 2.63/1.00  
% 2.63/1.00  fof(f79,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(equality_resolution,[],[f50])).
% 2.63/1.00  
% 2.63/1.00  fof(f80,plain,(
% 2.63/1.00    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(equality_resolution,[],[f79])).
% 2.63/1.00  
% 2.63/1.00  fof(f75,plain,(
% 2.63/1.00    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f72,plain,(
% 2.63/1.00    sK5 = sK7),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f71,plain,(
% 2.63/1.00    sK5 = sK6),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f70,plain,(
% 2.63/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f69,plain,(
% 2.63/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f68,plain,(
% 2.63/1.00    m1_subset_1(sK5,u1_struct_0(sK0))),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f74,plain,(
% 2.63/1.00    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f51,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f29])).
% 2.63/1.00  
% 2.63/1.00  fof(f77,plain,(
% 2.63/1.00    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(equality_resolution,[],[f51])).
% 2.63/1.00  
% 2.63/1.00  fof(f78,plain,(
% 2.63/1.00    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(equality_resolution,[],[f77])).
% 2.63/1.00  
% 2.63/1.00  fof(f73,plain,(
% 2.63/1.00    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  cnf(c_11,plain,
% 2.63/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_413,plain,
% 2.63/1.00      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1069,plain,
% 2.63/1.00      ( m1_pre_topc(X0_53,X0_53) = iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_26,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.63/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_398,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1081,plain,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.63/1.00      | ~ m1_pre_topc(X3,X4)
% 2.63/1.00      | ~ m1_pre_topc(X3,X1)
% 2.63/1.00      | ~ m1_pre_topc(X1,X4)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.63/1.00      | v2_struct_0(X4)
% 2.63/1.00      | v2_struct_0(X2)
% 2.63/1.00      | ~ v2_pre_topc(X2)
% 2.63/1.00      | ~ v2_pre_topc(X4)
% 2.63/1.00      | ~ l1_pre_topc(X4)
% 2.63/1.00      | ~ l1_pre_topc(X2)
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_420,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.63/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.63/1.00      | ~ m1_pre_topc(X3_53,X0_53)
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.63/1.00      | v2_struct_0(X2_53)
% 2.63/1.00      | v2_struct_0(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X2_53)
% 2.63/1.00      | ~ l1_pre_topc(X2_53)
% 2.63/1.00      | ~ l1_pre_topc(X1_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54)
% 2.63/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X3_53)) = k3_tmap_1(X2_53,X1_53,X0_53,X3_53,X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1062,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(X3_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X3_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2780,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK0,X0_53,sK2)
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK0,X1_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK1) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1081,c_1062]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_31,negated_conjecture,
% 2.63/1.00      ( ~ v2_struct_0(sK1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_38,plain,
% 2.63/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_30,negated_conjecture,
% 2.63/1.00      ( v2_pre_topc(sK1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_39,plain,
% 2.63/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_29,negated_conjecture,
% 2.63/1.00      ( l1_pre_topc(sK1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_40,plain,
% 2.63/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_28,negated_conjecture,
% 2.63/1.00      ( v1_funct_1(sK2) ),
% 2.63/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_41,plain,
% 2.63/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_27,negated_conjecture,
% 2.63/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_42,plain,
% 2.63/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2996,plain,
% 2.63/1.00      ( v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK0,X0_53,sK2)
% 2.63/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK0,X1_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2780,c_38,c_39,c_40,c_41,c_42]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2997,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK0,X0_53,sK2)
% 2.63/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK0,X1_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_2996]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3011,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k3_tmap_1(X0_53,sK1,sK0,X0_53,sK2)
% 2.63/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK0,X0_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1069,c_2997]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3670,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK2)
% 2.63/1.00      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1069,c_3011]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.63/1.00      | ~ m1_pre_topc(X3,X1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.63/1.00      | v2_struct_0(X1)
% 2.63/1.00      | v2_struct_0(X2)
% 2.63/1.00      | ~ v2_pre_topc(X2)
% 2.63/1.00      | ~ v2_pre_topc(X1)
% 2.63/1.00      | ~ l1_pre_topc(X1)
% 2.63/1.00      | ~ l1_pre_topc(X2)
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.63/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_421,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_pre_topc(X2_53,X0_53)
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.63/1.00      | v2_struct_0(X1_53)
% 2.63/1.00      | v2_struct_0(X0_53)
% 2.63/1.00      | ~ v2_pre_topc(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X0_53)
% 2.63/1.00      | ~ l1_pre_topc(X1_53)
% 2.63/1.00      | ~ l1_pre_topc(X0_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54)
% 2.63/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1061,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53)
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2424,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53)
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK1) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1081,c_1061]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_34,negated_conjecture,
% 2.63/1.00      ( ~ v2_struct_0(sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_35,plain,
% 2.63/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_33,negated_conjecture,
% 2.63/1.00      ( v2_pre_topc(sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_36,plain,
% 2.63/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_32,negated_conjecture,
% 2.63/1.00      ( l1_pre_topc(sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_37,plain,
% 2.63/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2849,plain,
% 2.63/1.00      ( m1_pre_topc(X0_53,sK0) != iProver_top
% 2.63/1.00      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53) ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2424,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2850,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53)
% 2.63/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_2849]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2859,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0)
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1069,c_2850]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_58,plain,
% 2.63/1.00      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1545,plain,
% 2.63/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.63/1.00      | ~ m1_pre_topc(X0_53,sK0)
% 2.63/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.00      | v2_struct_0(sK0)
% 2.63/1.00      | v2_struct_0(sK1)
% 2.63/1.00      | ~ v2_pre_topc(sK0)
% 2.63/1.00      | ~ v2_pre_topc(sK1)
% 2.63/1.00      | ~ l1_pre_topc(sK0)
% 2.63/1.00      | ~ l1_pre_topc(sK1)
% 2.63/1.00      | ~ v1_funct_1(sK2)
% 2.63/1.00      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_53)) = k2_tmap_1(sK0,sK1,sK2,X0_53) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_421]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1547,plain,
% 2.63/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.63/1.00      | ~ m1_pre_topc(sK0,sK0)
% 2.63/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.00      | v2_struct_0(sK0)
% 2.63/1.00      | v2_struct_0(sK1)
% 2.63/1.00      | ~ v2_pre_topc(sK0)
% 2.63/1.00      | ~ v2_pre_topc(sK1)
% 2.63/1.00      | ~ l1_pre_topc(sK0)
% 2.63/1.00      | ~ l1_pre_topc(sK1)
% 2.63/1.00      | ~ v1_funct_1(sK2)
% 2.63/1.00      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1545]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3054,plain,
% 2.63/1.00      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2859,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,
% 2.63/1.00                 c_58,c_1547]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3676,plain,
% 2.63/1.00      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK2) = k2_tmap_1(sK0,sK1,sK2,sK0)
% 2.63/1.00      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_3670,c_3054]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_57,plain,
% 2.63/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 2.63/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_59,plain,
% 2.63/1.00      ( m1_pre_topc(sK0,sK0) = iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_57]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3794,plain,
% 2.63/1.00      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK2) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3676,c_35,c_36,c_37,c_59]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_12,plain,
% 2.63/1.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 2.63/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.63/1.00      | ~ m1_pre_topc(X0,X3)
% 2.63/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.63/1.00      | v2_struct_0(X3)
% 2.63/1.00      | v2_struct_0(X1)
% 2.63/1.00      | v2_struct_0(X0)
% 2.63/1.00      | ~ v2_pre_topc(X1)
% 2.63/1.00      | ~ v2_pre_topc(X3)
% 2.63/1.00      | ~ l1_pre_topc(X3)
% 2.63/1.00      | ~ l1_pre_topc(X1)
% 2.63/1.00      | ~ v1_funct_1(X2) ),
% 2.63/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_412,plain,
% 2.63/1.00      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54))
% 2.63/1.00      | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.63/1.00      | v2_struct_0(X1_53)
% 2.63/1.00      | v2_struct_0(X0_53)
% 2.63/1.00      | v2_struct_0(X2_53)
% 2.63/1.00      | ~ v2_pre_topc(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X2_53)
% 2.63/1.00      | ~ l1_pre_topc(X1_53)
% 2.63/1.00      | ~ l1_pre_topc(X2_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1070,plain,
% 2.63/1.00      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54)) = iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3797,plain,
% 2.63/1.00      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) = iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK1) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3794,c_1070]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_43,plain,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3849,plain,
% 2.63/1.00      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3797,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,
% 2.63/1.00                 c_59]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_5,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.63/1.00      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.63/1.00      | ~ l1_struct_0(X3)
% 2.63/1.00      | ~ l1_struct_0(X2)
% 2.63/1.00      | ~ l1_struct_0(X1)
% 2.63/1.00      | ~ v1_funct_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_419,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.63/1.00      | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.63/1.00      | ~ l1_struct_0(X2_53)
% 2.63/1.00      | ~ l1_struct_0(X1_53)
% 2.63/1.00      | ~ l1_struct_0(X0_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1063,plain,
% 2.63/1.00      ( v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
% 2.63/1.00      | l1_struct_0(X2_53) != iProver_top
% 2.63/1.00      | l1_struct_0(X1_53) != iProver_top
% 2.63/1.00      | l1_struct_0(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1,plain,
% 2.63/1.00      ( ~ r2_funct_2(X0,X1,X2,X3)
% 2.63/1.00      | ~ v1_funct_2(X3,X0,X1)
% 2.63/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.63/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.63/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.63/1.00      | ~ v1_funct_1(X3)
% 2.63/1.00      | ~ v1_funct_1(X2)
% 2.63/1.00      | X2 = X3 ),
% 2.63/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_423,plain,
% 2.63/1.00      ( ~ r2_funct_2(X0_55,X1_55,X0_54,X1_54)
% 2.63/1.00      | ~ v1_funct_2(X1_54,X0_55,X1_55)
% 2.63/1.00      | ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.63/1.00      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.63/1.00      | ~ v1_funct_1(X0_54)
% 2.63/1.00      | ~ v1_funct_1(X1_54)
% 2.63/1.00      | X0_54 = X1_54 ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1059,plain,
% 2.63/1.00      ( X0_54 = X1_54
% 2.63/1.00      | r2_funct_2(X0_55,X1_55,X0_54,X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.63/1.00      | v1_funct_2(X1_54,X0_55,X1_55) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.63/1.00      | v1_funct_1(X1_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1976,plain,
% 2.63/1.00      ( sK2 = X0_54
% 2.63/1.00      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1081,c_1059]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2342,plain,
% 2.63/1.00      ( v1_funct_1(X0_54) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | sK2 = X0_54
% 2.63/1.00      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_1976,c_41,c_42]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2343,plain,
% 2.63/1.00      ( sK2 = X0_54
% 2.63/1.00      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_2342]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2578,plain,
% 2.63/1.00      ( k2_tmap_1(X0_53,sK1,X0_54,sK0) = sK2
% 2.63/1.00      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(X0_53) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.63/1.00      | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1063,c_2343]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2,plain,
% 2.63/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_82,plain,
% 2.63/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_84,plain,
% 2.63/1.00      ( l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) = iProver_top ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_82]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_422,plain,
% 2.63/1.00      ( ~ l1_pre_topc(X0_53) | l1_struct_0(X0_53) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1924,plain,
% 2.63/1.00      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_422]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1925,plain,
% 2.63/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3129,plain,
% 2.63/1.00      ( k2_tmap_1(X0_53,sK1,X0_54,sK0) = sK2
% 2.63/1.00      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.63/1.00      | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK0)) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2578,c_37,c_40,c_84,c_1925]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3854,plain,
% 2.63/1.00      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2
% 2.63/1.00      | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK0)) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3849,c_3129]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_7,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.63/1.00      | ~ l1_struct_0(X3)
% 2.63/1.00      | ~ l1_struct_0(X2)
% 2.63/1.00      | ~ l1_struct_0(X1)
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_417,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.63/1.00      | ~ l1_struct_0(X2_53)
% 2.63/1.00      | ~ l1_struct_0(X1_53)
% 2.63/1.00      | ~ l1_struct_0(X0_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54)
% 2.63/1.00      | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53)) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1518,plain,
% 2.63/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.63/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.00      | ~ l1_struct_0(X0_53)
% 2.63/1.00      | ~ l1_struct_0(sK0)
% 2.63/1.00      | ~ l1_struct_0(sK1)
% 2.63/1.00      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0_53))
% 2.63/1.00      | ~ v1_funct_1(sK2) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_417]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1519,plain,
% 2.63/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(X0_53) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0_53)) = iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1521,plain,
% 2.63/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK0)) = iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1519]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_6,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.63/1.00      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.63/1.00      | ~ l1_struct_0(X3)
% 2.63/1.00      | ~ l1_struct_0(X2)
% 2.63/1.00      | ~ l1_struct_0(X1)
% 2.63/1.00      | ~ v1_funct_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_418,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.63/1.00      | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.63/1.00      | ~ l1_struct_0(X2_53)
% 2.63/1.00      | ~ l1_struct_0(X1_53)
% 2.63/1.00      | ~ l1_struct_0(X0_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1523,plain,
% 2.63/1.00      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0_53),u1_struct_0(X0_53),u1_struct_0(sK1))
% 2.63/1.00      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.63/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.00      | ~ l1_struct_0(X0_53)
% 2.63/1.00      | ~ l1_struct_0(sK0)
% 2.63/1.00      | ~ l1_struct_0(sK1)
% 2.63/1.00      | ~ v1_funct_1(sK2) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_418]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1524,plain,
% 2.63/1.00      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0_53),u1_struct_0(X0_53),u1_struct_0(sK1)) = iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(X0_53) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1526,plain,
% 2.63/1.00      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_1524]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2708,plain,
% 2.63/1.00      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2
% 2.63/1.00      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tmap_1(sK0,sK1,sK2,sK0)) != iProver_top
% 2.63/1.00      | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | l1_struct_0(sK0) != iProver_top
% 2.63/1.00      | l1_struct_0(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK0)) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_2578]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3857,plain,
% 2.63/1.00      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3854,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,
% 2.63/1.00                 c_59,c_84,c_1521,c_1526,c_1925,c_2708,c_3797]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_21,negated_conjecture,
% 2.63/1.00      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 2.63/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_403,negated_conjecture,
% 2.63/1.00      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_10,plain,
% 2.63/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.63/1.00      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 2.63/1.00      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.63/1.00      | ~ m1_pre_topc(X0,X2)
% 2.63/1.00      | ~ m1_pre_topc(X5,X2)
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 2.63/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.63/1.00      | v2_struct_0(X2)
% 2.63/1.00      | v2_struct_0(X1)
% 2.63/1.00      | v2_struct_0(X0)
% 2.63/1.00      | v2_struct_0(X5)
% 2.63/1.00      | ~ v2_pre_topc(X1)
% 2.63/1.00      | ~ v2_pre_topc(X2)
% 2.63/1.00      | ~ l1_pre_topc(X2)
% 2.63/1.00      | ~ l1_pre_topc(X1)
% 2.63/1.00      | ~ v1_funct_1(X3) ),
% 2.63/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_414,plain,
% 2.63/1.00      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
% 2.63/1.00      | ~ r1_tmap_1(k1_tsep_1(X2_53,X0_53,X3_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X0_53,X3_53)),X1_54)
% 2.63/1.00      | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.63/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X3_53))
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X0_53,X3_53)))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.63/1.00      | v2_struct_0(X3_53)
% 2.63/1.00      | v2_struct_0(X1_53)
% 2.63/1.00      | v2_struct_0(X0_53)
% 2.63/1.00      | v2_struct_0(X2_53)
% 2.63/1.00      | ~ v2_pre_topc(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X2_53)
% 2.63/1.00      | ~ l1_pre_topc(X1_53)
% 2.63/1.00      | ~ l1_pre_topc(X2_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1068,plain,
% 2.63/1.00      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(k1_tsep_1(X2_53,X0_53,X3_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X0_53,X3_53)),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X3_53,X2_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(X3_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X0_53,X3_53))) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3426,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK3) = iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK4) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_403,c_1068]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3446,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK3) = iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK4) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_3426,c_403]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_25,negated_conjecture,
% 2.63/1.00      ( ~ v2_struct_0(sK3) ),
% 2.63/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_44,plain,
% 2.63/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_24,negated_conjecture,
% 2.63/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_45,plain,
% 2.63/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_23,negated_conjecture,
% 2.63/1.00      ( ~ v2_struct_0(sK4) ),
% 2.63/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_46,plain,
% 2.63/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_22,negated_conjecture,
% 2.63/1.00      ( m1_pre_topc(sK4,sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_47,plain,
% 2.63/1.00      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3469,plain,
% 2.63/1.00      ( l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3446,c_35,c_36,c_37,c_44,c_45,c_46,c_47]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3470,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_3469]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3875,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | v2_struct_0(sK1) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3857,c_3470]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4364,plain,
% 2.63/1.00      ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3875,c_38,c_39,c_40,c_41,c_42,c_43]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4365,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_4364]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_9,plain,
% 2.63/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.63/1.00      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.63/1.00      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.63/1.00      | ~ m1_pre_topc(X5,X2)
% 2.63/1.00      | ~ m1_pre_topc(X0,X2)
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.63/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.63/1.00      | v2_struct_0(X2)
% 2.63/1.00      | v2_struct_0(X1)
% 2.63/1.00      | v2_struct_0(X5)
% 2.63/1.00      | v2_struct_0(X0)
% 2.63/1.00      | ~ v2_pre_topc(X1)
% 2.63/1.00      | ~ v2_pre_topc(X2)
% 2.63/1.00      | ~ l1_pre_topc(X2)
% 2.63/1.00      | ~ l1_pre_topc(X1)
% 2.63/1.00      | ~ v1_funct_1(X3) ),
% 2.63/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_415,plain,
% 2.63/1.00      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
% 2.63/1.00      | ~ r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54)
% 2.63/1.00      | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.63/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X3_53))
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53)))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.63/1.00      | v2_struct_0(X3_53)
% 2.63/1.00      | v2_struct_0(X1_53)
% 2.63/1.00      | v2_struct_0(X0_53)
% 2.63/1.00      | v2_struct_0(X2_53)
% 2.63/1.00      | ~ v2_pre_topc(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X2_53)
% 2.63/1.00      | ~ l1_pre_topc(X1_53)
% 2.63/1.00      | ~ l1_pre_topc(X2_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1067,plain,
% 2.63/1.00      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X3_53,X2_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(X3_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53))) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3272,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK3) = iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK4) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_403,c_1067]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3292,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK3) = iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK4) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_3272,c_403]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3315,plain,
% 2.63/1.00      ( l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3292,c_35,c_36,c_37,c_44,c_45,c_46,c_47]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3316,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) = iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_3315]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3876,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_54) = iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | v2_struct_0(sK1) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_3857,c_3316]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4475,plain,
% 2.63/1.00      ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_54) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3876,c_38,c_39,c_40,c_41,c_42,c_43]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4476,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,X0_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_54) = iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_4475]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_13,negated_conjecture,
% 2.63/1.00      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.63/1.00      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.63/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.63/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_411,negated_conjecture,
% 2.63/1.00      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.63/1.00      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.63/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1071,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_16,negated_conjecture,
% 2.63/1.00      ( sK5 = sK7 ),
% 2.63/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_408,negated_conjecture,
% 2.63/1.00      ( sK5 = sK7 ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_17,negated_conjecture,
% 2.63/1.00      ( sK5 = sK6 ),
% 2.63/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_407,negated_conjecture,
% 2.63/1.00      ( sK5 = sK6 ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1092,plain,
% 2.63/1.00      ( sK6 = sK7 ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_407,c_408]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1157,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_1071,c_408,c_1092]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4486,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_4476,c_1157]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_18,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_50,plain,
% 2.63/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_19,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_405,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1075,plain,
% 2.63/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1119,plain,
% 2.63/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_1075,c_1092]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_20,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_404,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1076,plain,
% 2.63/1.00      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1122,plain,
% 2.63/1.00      ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_1076,c_408]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_14,negated_conjecture,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.63/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_410,negated_conjecture,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1072,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1139,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_1072,c_408]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_8,plain,
% 2.63/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.63/1.00      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 2.63/1.00      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.63/1.00      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.63/1.00      | ~ m1_pre_topc(X5,X2)
% 2.63/1.00      | ~ m1_pre_topc(X0,X2)
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.63/1.00      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.63/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.63/1.00      | v2_struct_0(X2)
% 2.63/1.00      | v2_struct_0(X1)
% 2.63/1.00      | v2_struct_0(X5)
% 2.63/1.00      | v2_struct_0(X0)
% 2.63/1.00      | ~ v2_pre_topc(X1)
% 2.63/1.00      | ~ v2_pre_topc(X2)
% 2.63/1.00      | ~ l1_pre_topc(X2)
% 2.63/1.00      | ~ l1_pre_topc(X1)
% 2.63/1.00      | ~ v1_funct_1(X3) ),
% 2.63/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_416,plain,
% 2.63/1.00      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
% 2.63/1.00      | ~ r1_tmap_1(X3_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X3_53),X1_54)
% 2.63/1.00      | r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54)
% 2.63/1.00      | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 2.63/1.00      | ~ m1_pre_topc(X0_53,X2_53)
% 2.63/1.00      | ~ m1_pre_topc(X3_53,X2_53)
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X3_53))
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(X0_53))
% 2.63/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53)))
% 2.63/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.63/1.00      | v2_struct_0(X3_53)
% 2.63/1.00      | v2_struct_0(X1_53)
% 2.63/1.00      | v2_struct_0(X0_53)
% 2.63/1.00      | v2_struct_0(X2_53)
% 2.63/1.00      | ~ v2_pre_topc(X1_53)
% 2.63/1.00      | ~ v2_pre_topc(X2_53)
% 2.63/1.00      | ~ l1_pre_topc(X1_53)
% 2.63/1.00      | ~ l1_pre_topc(X2_53)
% 2.63/1.00      | ~ v1_funct_1(X0_54) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1066,plain,
% 2.63/1.00      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(X3_53,X1_53,k2_tmap_1(X2_53,X1_53,X0_54,X3_53),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(k1_tsep_1(X2_53,X3_53,X0_53),X1_53,k2_tmap_1(X2_53,X1_53,X0_54,k1_tsep_1(X2_53,X3_53,X0_53)),X1_54) = iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.63/1.00      | m1_pre_topc(X3_53,X2_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(X3_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(X2_53,X3_53,X0_53))) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(X2_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X2_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3206,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK3) = iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK4) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_403,c_1066]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3208,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.63/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_struct_0(sK3) = iProver_top
% 2.63/1.00      | v2_struct_0(sK0) = iProver_top
% 2.63/1.00      | v2_struct_0(sK4) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_3206,c_403]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3579,plain,
% 2.63/1.00      ( l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3208,c_35,c_36,c_37,c_44,c_45,c_46,c_47]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3580,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK3),X1_54) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK0),X1_54) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK4,X0_53,k2_tmap_1(sK0,X0_53,X0_54,sK4),X1_54) != iProver_top
% 2.63/1.00      | v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.63/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.63/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_3579]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3597,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK7) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.63/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.00      | v2_struct_0(sK1) = iProver_top
% 2.63/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.63/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.63/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1139,c_3580]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_15,negated_conjecture,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 2.63/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_409,negated_conjecture,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1073,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1144,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_1073,c_408,c_1092]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3600,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK7) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_3597,c_38,c_39,c_40,c_41,c_42,c_43,c_50,c_1119,c_1144,
% 2.63/1.00                 c_1122]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3601,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),sK7) = iProver_top
% 2.63/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 2.63/1.00      inference(renaming,[status(thm)],[c_3600]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3862,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_3857,c_3601]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4513,plain,
% 2.63/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_4486,c_50,c_1119,c_1122,c_3862]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4519,plain,
% 2.63/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.63/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_4365,c_4513]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(contradiction,plain,
% 2.63/1.00      ( $false ),
% 2.63/1.00      inference(minisat,[status(thm)],[c_4519,c_3862,c_1122,c_1119,c_50]) ).
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  ------                               Statistics
% 2.63/1.00  
% 2.63/1.00  ------ General
% 2.63/1.00  
% 2.63/1.00  abstr_ref_over_cycles:                  0
% 2.63/1.00  abstr_ref_under_cycles:                 0
% 2.63/1.00  gc_basic_clause_elim:                   0
% 2.63/1.00  forced_gc_time:                         0
% 2.63/1.00  parsing_time:                           0.026
% 2.63/1.00  unif_index_cands_time:                  0.
% 2.63/1.00  unif_index_add_time:                    0.
% 2.63/1.00  orderings_time:                         0.
% 2.63/1.00  out_proof_time:                         0.02
% 2.63/1.00  total_time:                             0.232
% 2.63/1.00  num_of_symbols:                         57
% 2.63/1.00  num_of_terms:                           4535
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing
% 2.63/1.00  
% 2.63/1.00  num_of_splits:                          0
% 2.63/1.00  num_of_split_atoms:                     0
% 2.63/1.00  num_of_reused_defs:                     0
% 2.63/1.00  num_eq_ax_congr_red:                    16
% 2.63/1.00  num_of_sem_filtered_clauses:            1
% 2.63/1.00  num_of_subtypes:                        4
% 2.63/1.00  monotx_restored_types:                  0
% 2.63/1.00  sat_num_of_epr_types:                   0
% 2.63/1.00  sat_num_of_non_cyclic_types:            0
% 2.63/1.00  sat_guarded_non_collapsed_types:        1
% 2.63/1.00  num_pure_diseq_elim:                    0
% 2.63/1.00  simp_replaced_by:                       0
% 2.63/1.00  res_preprocessed:                       148
% 2.63/1.00  prep_upred:                             0
% 2.63/1.00  prep_unflattend:                        8
% 2.63/1.00  smt_new_axioms:                         0
% 2.63/1.00  pred_elim_cands:                        10
% 2.63/1.00  pred_elim:                              0
% 2.63/1.00  pred_elim_cl:                           0
% 2.63/1.00  pred_elim_cycles:                       1
% 2.63/1.00  merged_defs:                            0
% 2.63/1.00  merged_defs_ncl:                        0
% 2.63/1.00  bin_hyper_res:                          0
% 2.63/1.00  prep_cycles:                            3
% 2.63/1.00  pred_elim_time:                         0.002
% 2.63/1.00  splitting_time:                         0.
% 2.63/1.00  sem_filter_time:                        0.
% 2.63/1.00  monotx_time:                            0.
% 2.63/1.00  subtype_inf_time:                       0.001
% 2.63/1.00  
% 2.63/1.00  ------ Problem properties
% 2.63/1.00  
% 2.63/1.00  clauses:                                35
% 2.63/1.00  conjectures:                            22
% 2.63/1.00  epr:                                    15
% 2.63/1.00  horn:                                   27
% 2.63/1.00  ground:                                 22
% 2.63/1.00  unary:                                  19
% 2.63/1.00  binary:                                 4
% 2.63/1.00  lits:                                   154
% 2.63/1.00  lits_eq:                                6
% 2.63/1.00  fd_pure:                                0
% 2.63/1.00  fd_pseudo:                              0
% 2.63/1.00  fd_cond:                                0
% 2.63/1.00  fd_pseudo_cond:                         1
% 2.63/1.00  ac_symbols:                             0
% 2.63/1.00  
% 2.63/1.00  ------ Propositional Solver
% 2.63/1.00  
% 2.63/1.00  prop_solver_calls:                      23
% 2.63/1.00  prop_fast_solver_calls:                 1782
% 2.63/1.00  smt_solver_calls:                       0
% 2.63/1.00  smt_fast_solver_calls:                  0
% 2.63/1.00  prop_num_of_clauses:                    1299
% 2.63/1.00  prop_preprocess_simplified:             5023
% 2.63/1.00  prop_fo_subsumed:                       114
% 2.63/1.00  prop_solver_time:                       0.
% 2.63/1.00  smt_solver_time:                        0.
% 2.63/1.00  smt_fast_solver_time:                   0.
% 2.63/1.00  prop_fast_solver_time:                  0.
% 2.63/1.00  prop_unsat_core_time:                   0.
% 2.63/1.00  
% 2.63/1.00  ------ QBF
% 2.63/1.00  
% 2.63/1.00  qbf_q_res:                              0
% 2.63/1.00  qbf_num_tautologies:                    0
% 2.63/1.00  qbf_prep_cycles:                        0
% 2.63/1.00  
% 2.63/1.00  ------ BMC1
% 2.63/1.00  
% 2.63/1.00  bmc1_current_bound:                     -1
% 2.63/1.00  bmc1_last_solved_bound:                 -1
% 2.63/1.00  bmc1_unsat_core_size:                   -1
% 2.63/1.00  bmc1_unsat_core_parents_size:           -1
% 2.63/1.00  bmc1_merge_next_fun:                    0
% 2.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation
% 2.63/1.00  
% 2.63/1.00  inst_num_of_clauses:                    412
% 2.63/1.00  inst_num_in_passive:                    25
% 2.63/1.00  inst_num_in_active:                     314
% 2.63/1.00  inst_num_in_unprocessed:                73
% 2.63/1.00  inst_num_of_loops:                      330
% 2.63/1.00  inst_num_of_learning_restarts:          0
% 2.63/1.00  inst_num_moves_active_passive:          12
% 2.63/1.00  inst_lit_activity:                      0
% 2.63/1.00  inst_lit_activity_moves:                0
% 2.63/1.00  inst_num_tautologies:                   0
% 2.63/1.00  inst_num_prop_implied:                  0
% 2.63/1.00  inst_num_existing_simplified:           0
% 2.63/1.00  inst_num_eq_res_simplified:             0
% 2.63/1.00  inst_num_child_elim:                    0
% 2.63/1.00  inst_num_of_dismatching_blockings:      139
% 2.63/1.00  inst_num_of_non_proper_insts:           430
% 2.63/1.00  inst_num_of_duplicates:                 0
% 2.63/1.00  inst_inst_num_from_inst_to_res:         0
% 2.63/1.00  inst_dismatching_checking_time:         0.
% 2.63/1.00  
% 2.63/1.00  ------ Resolution
% 2.63/1.00  
% 2.63/1.00  res_num_of_clauses:                     0
% 2.63/1.00  res_num_in_passive:                     0
% 2.63/1.00  res_num_in_active:                      0
% 2.63/1.00  res_num_of_loops:                       151
% 2.63/1.00  res_forward_subset_subsumed:            53
% 2.63/1.00  res_backward_subset_subsumed:           0
% 2.63/1.00  res_forward_subsumed:                   0
% 2.63/1.00  res_backward_subsumed:                  0
% 2.63/1.00  res_forward_subsumption_resolution:     0
% 2.63/1.00  res_backward_subsumption_resolution:    0
% 2.63/1.00  res_clause_to_clause_subsumption:       222
% 2.63/1.00  res_orphan_elimination:                 0
% 2.63/1.00  res_tautology_del:                      41
% 2.63/1.00  res_num_eq_res_simplified:              0
% 2.63/1.00  res_num_sel_changes:                    0
% 2.63/1.00  res_moves_from_active_to_pass:          0
% 2.63/1.00  
% 2.63/1.00  ------ Superposition
% 2.63/1.00  
% 2.63/1.00  sup_time_total:                         0.
% 2.63/1.00  sup_time_generating:                    0.
% 2.63/1.00  sup_time_sim_full:                      0.
% 2.63/1.00  sup_time_sim_immed:                     0.
% 2.63/1.00  
% 2.63/1.00  sup_num_of_clauses:                     69
% 2.63/1.00  sup_num_in_active:                      60
% 2.63/1.00  sup_num_in_passive:                     9
% 2.63/1.00  sup_num_of_loops:                       65
% 2.63/1.00  sup_fw_superposition:                   38
% 2.63/1.00  sup_bw_superposition:                   19
% 2.63/1.00  sup_immediate_simplified:               18
% 2.63/1.00  sup_given_eliminated:                   0
% 2.63/1.00  comparisons_done:                       0
% 2.63/1.00  comparisons_avoided:                    0
% 2.63/1.00  
% 2.63/1.00  ------ Simplifications
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  sim_fw_subset_subsumed:                 5
% 2.63/1.00  sim_bw_subset_subsumed:                 3
% 2.63/1.00  sim_fw_subsumed:                        2
% 2.63/1.00  sim_bw_subsumed:                        0
% 2.63/1.00  sim_fw_subsumption_res:                 4
% 2.63/1.00  sim_bw_subsumption_res:                 0
% 2.63/1.00  sim_tautology_del:                      6
% 2.63/1.00  sim_eq_tautology_del:                   3
% 2.63/1.00  sim_eq_res_simp:                        0
% 2.63/1.00  sim_fw_demodulated:                     0
% 2.63/1.00  sim_bw_demodulated:                     4
% 2.63/1.00  sim_light_normalised:                   18
% 2.63/1.00  sim_joinable_taut:                      0
% 2.63/1.00  sim_joinable_simp:                      0
% 2.63/1.00  sim_ac_normalised:                      0
% 2.63/1.00  sim_smt_subsumption:                    0
% 2.63/1.00  
%------------------------------------------------------------------------------
