%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:22 EST 2020

% Result     : Theorem 19.47s
% Output     : CNFRefutation 19.47s
% Verified   : 
% Statistics : Number of formulae       :  632 (157727122 expanded)
%              Number of clauses        :  543 (27065702 expanded)
%              Number of leaves         :   20 (49898791 expanded)
%              Depth                    :   63
%              Number of atoms          : 3375 (2971821664 expanded)
%              Number of equality atoms : 1606 (160303154 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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
             => ( k1_tsep_1(X0,X1,X2) = X0
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                             => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v5_pre_topc(X4,X0,X3)
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( k1_tsep_1(X0,X1,X2) = X0
                 => ( r3_tsep_1(X0,X1,X2)
                  <=> ( ! [X3] :
                          ( ( l1_pre_topc(X3)
                            & v2_pre_topc(X3)
                            & ~ v2_struct_0(X3) )
                         => ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) )
                             => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                  & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                               => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                  & v5_pre_topc(X4,X0,X3)
                                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                  & v1_funct_1(X4) ) ) ) )
                      & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f18,plain,(
    ! [X3,X0,X2,X1] :
      ( sP1(X3,X0,X2,X1)
    <=> ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v5_pre_topc(X4,X0,X3)
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) )
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( sP1(X3,X0,X2,X1)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP1(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( sP1(X3,X0,X2,X1)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP1(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( sP1(X3,X0,X2,X1)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP1(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( sP1(X4,X0,X2,X1)
                      | ~ l1_pre_topc(X4)
                      | ~ v2_pre_topc(X4)
                      | v2_struct_0(X4) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ sP1(X3,X0,X2,X1)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP1(sK8,X0,X2,X1)
        & l1_pre_topc(sK8)
        & v2_pre_topc(sK8)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ sP1(X3,X0,X2,X1)
                & l1_pre_topc(X3)
                & v2_pre_topc(X3)
                & ~ v2_struct_0(X3) )
            | ~ r1_tsep_1(X1,X2)
            | ~ r3_tsep_1(X0,X1,X2) )
          & ( ( ! [X4] :
                  ( sP1(X4,X0,X2,X1)
                  | ~ l1_pre_topc(X4)
                  | ~ v2_pre_topc(X4)
                  | v2_struct_0(X4) )
              & r1_tsep_1(X1,X2) )
            | r3_tsep_1(X0,X1,X2) )
          & k1_tsep_1(X0,X1,X2) = X0
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ? [X3] :
              ( ~ sP1(X3,X0,sK7,X1)
              & l1_pre_topc(X3)
              & v2_pre_topc(X3)
              & ~ v2_struct_0(X3) )
          | ~ r1_tsep_1(X1,sK7)
          | ~ r3_tsep_1(X0,X1,sK7) )
        & ( ( ! [X4] :
                ( sP1(X4,X0,sK7,X1)
                | ~ l1_pre_topc(X4)
                | ~ v2_pre_topc(X4)
                | v2_struct_0(X4) )
            & r1_tsep_1(X1,sK7) )
          | r3_tsep_1(X0,X1,sK7) )
        & k1_tsep_1(X0,X1,sK7) = X0
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP1(X3,X0,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( sP1(X4,X0,X2,X1)
                      | ~ l1_pre_topc(X4)
                      | ~ v2_pre_topc(X4)
                      | v2_struct_0(X4) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ sP1(X3,X0,X2,sK6)
                  & l1_pre_topc(X3)
                  & v2_pre_topc(X3)
                  & ~ v2_struct_0(X3) )
              | ~ r1_tsep_1(sK6,X2)
              | ~ r3_tsep_1(X0,sK6,X2) )
            & ( ( ! [X4] :
                    ( sP1(X4,X0,X2,sK6)
                    | ~ l1_pre_topc(X4)
                    | ~ v2_pre_topc(X4)
                    | v2_struct_0(X4) )
                & r1_tsep_1(sK6,X2) )
              | r3_tsep_1(X0,sK6,X2) )
            & k1_tsep_1(X0,sK6,X2) = X0
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ sP1(X3,X0,X2,X1)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( ( ! [X4] :
                        ( sP1(X4,X0,X2,X1)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | r3_tsep_1(X0,X1,X2) )
                & k1_tsep_1(X0,X1,X2) = X0
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ sP1(X3,sK5,X2,X1)
                    & l1_pre_topc(X3)
                    & v2_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                | ~ r1_tsep_1(X1,X2)
                | ~ r3_tsep_1(sK5,X1,X2) )
              & ( ( ! [X4] :
                      ( sP1(X4,sK5,X2,X1)
                      | ~ l1_pre_topc(X4)
                      | ~ v2_pre_topc(X4)
                      | v2_struct_0(X4) )
                  & r1_tsep_1(X1,X2) )
                | r3_tsep_1(sK5,X1,X2) )
              & k1_tsep_1(sK5,X1,X2) = sK5
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ( ~ sP1(sK8,sK5,sK7,sK6)
        & l1_pre_topc(sK8)
        & v2_pre_topc(sK8)
        & ~ v2_struct_0(sK8) )
      | ~ r1_tsep_1(sK6,sK7)
      | ~ r3_tsep_1(sK5,sK6,sK7) )
    & ( ( ! [X4] :
            ( sP1(X4,sK5,sK7,sK6)
            | ~ l1_pre_topc(X4)
            | ~ v2_pre_topc(X4)
            | v2_struct_0(X4) )
        & r1_tsep_1(sK6,sK7) )
      | r3_tsep_1(sK5,sK6,sK7) )
    & k1_tsep_1(sK5,sK6,sK7) = sK5
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f35,f39,f38,f37,f36])).

fof(f89,plain,(
    k1_tsep_1(sK5,sK6,sK7) = sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( sP0(X3,X2,X1,X0)
    <=> ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(X4) )
          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP0(X3,X2,X1,X0)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
            & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
            & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
            & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(X4) )
            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
            | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
            | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP0(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0)
            & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4))
            & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0)
            & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5))
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4))
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
          | ~ v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          | ~ v1_funct_1(sK2(X0,X1,X2,X3)) )
        & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0)
        & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)))
        & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0)
        & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)))
        & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(sK2(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(sK2(X0,X1,X2,X3)) )
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)))
          & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0)
          & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)))
          & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(sK2(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5))
            | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0)
            | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(sK2(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f42,plain,(
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

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
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
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) )
                           => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( sP0(X3,X2,X1,X0)
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP0(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( sP0(X3,X2,X1,X0)
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP0(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X3] :
                        ( sP0(X3,X2,X1,X0)
                        | ~ l1_pre_topc(X3)
                        | ~ v2_pre_topc(X3)
                        | v2_struct_0(X3) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ? [X3] :
                      ( ~ sP0(X3,X2,X1,X0)
                      & l1_pre_topc(X3)
                      & v2_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X4] :
                        ( sP0(X4,X2,X1,X0)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X3,X2,X1,X0)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
        & l1_pre_topc(sK3(X0,X1,X2))
        & v2_pre_topc(sK3(X0,X1,X2))
        & ~ v2_struct_0(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_tsep_1(X0,X1,X2)
                  | ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
                    & l1_pre_topc(sK3(X0,X1,X2))
                    & v2_pre_topc(sK3(X0,X1,X2))
                    & ~ v2_struct_0(sK3(X0,X1,X2)) )
                  | ~ r1_tsep_1(X1,X2) )
                & ( ( ! [X4] :
                        ( sP0(X4,X2,X1,X0)
                        | ~ l1_pre_topc(X4)
                        | ~ v2_pre_topc(X4)
                        | v2_struct_0(X4) )
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,
    ( r1_tsep_1(sK6,sK7)
    | r3_tsep_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | ~ v2_struct_0(sK3(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | v2_pre_topc(sK3(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_tsep_1(X0,X1,X2)
      | l1_pre_topc(sK3(X0,X1,X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP1(X3,X0,X2,X1)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              | ~ v5_pre_topc(X4,X0,X3)
              | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v5_pre_topc(X4,X0,X3)
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(X4) )
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP1(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v5_pre_topc(X4,X1,X0)
              | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
            & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
            & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
            & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X1,X0,X4,X3))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(X5,X1,X0)
              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X4,X1,X0)
            | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
          & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,X4,X3))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
          | ~ v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(sK4(X0,X1,X2,X3)) )
        & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0)
        & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2))
        & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0)
        & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3))
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
            | ~ v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(sK4(X0,X1,X2,X3)) )
          & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2))
          & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3))
          & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(sK4(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(X5,X1,X0)
              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f41,plain,(
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

fof(f95,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ r3_tsep_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( ~ v2_struct_0(sK8)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ r3_tsep_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( v2_pre_topc(sK8)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ r3_tsep_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,
    ( l1_pre_topc(sK8)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ r3_tsep_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v5_pre_topc(X5,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
      | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
      | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
      | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X5)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X4] :
      ( sP1(X4,sK5,sK7,sK6)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r3_tsep_1(sK5,sK6,sK7) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0)
      | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5))
      | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0)
      | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(X5)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(sK2(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
      | ~ v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X4,X2,X1,X0)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_47,negated_conjecture,
    ( k1_tsep_1(sK5,sK6,sK7) = sK5 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8387,negated_conjecture,
    ( k1_tsep_1(sK5,sK6,sK7) = sK5 ),
    inference(subtyping,[status(esa)],[c_47])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8411,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | m1_subset_1(sK2(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_9331,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | m1_subset_1(sK2(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8411])).

cnf(c_10985,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_subset_1(sK2(X0_54,sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9331])).

cnf(c_48,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8386,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_9355,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8386])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(sK2(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8409,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_1(sK2(X0_54,X1_54,X2_54,X3_54)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_9333,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_1(sK2(X0_54,X1_54,X2_54,X3_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8409])).

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
    inference(cnf_transformation,[],[f42])).

cnf(c_8420,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9322,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55)
    | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8420])).

cnf(c_11065,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_2(sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | m1_pre_topc(sK5,X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_9322])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8410,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_2(sK2(X0_54,X1_54,X2_54,X3_54),u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_9332,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_2(sK2(X0_54,X1_54,X2_54,X3_54),u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8410])).

cnf(c_10527,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_2(sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9332])).

cnf(c_11292,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | m1_pre_topc(sK5,X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11065,c_10527])).

cnf(c_11293,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | m1_pre_topc(sK5,X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11292])).

cnf(c_11298,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | m1_pre_topc(sK5,X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9333,c_11293])).

cnf(c_11418,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(X1_54,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(sK7,X1_54) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9355,c_11298])).

cnf(c_11494,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9355,c_11418])).

cnf(c_54,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_55,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_56,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_57,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_11503,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11494,c_55,c_56,c_57])).

cnf(c_11504,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_11503])).

cnf(c_18,plain,
    ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
    | r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8407,plain,
    ( ~ sP0(sK3(X0_54,X1_54,X2_54),X2_54,X1_54,X0_54)
    | r3_tsep_1(X0_54,X1_54,X2_54)
    | ~ r1_tsep_1(X1_54,X2_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_9335,plain,
    ( sP0(sK3(X0_54,X1_54,X2_54),X2_54,X1_54,X0_54) != iProver_top
    | r3_tsep_1(X0_54,X1_54,X2_54) = iProver_top
    | r1_tsep_1(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8407])).

cnf(c_12743,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11504,c_9335])).

cnf(c_51,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_58,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_59,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_60,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_61,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_23,plain,
    ( ~ r3_tsep_1(X0,X1,X2)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_46,negated_conjecture,
    ( r3_tsep_1(sK5,sK6,sK7)
    | r1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3558,plain,
    ( r1_tsep_1(X0,X1)
    | r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | sK6 != X0
    | sK7 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_46])).

cnf(c_3559,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_3558])).

cnf(c_3560,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3559])).

cnf(c_21,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(sK3(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8404,plain,
    ( r3_tsep_1(X0_54,X1_54,X2_54)
    | ~ r1_tsep_1(X1_54,X2_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v2_struct_0(sK3(X0_54,X1_54,X2_54))
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_9432,plain,
    ( r3_tsep_1(sK5,X0_54,X1_54)
    | ~ r1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,sK5)
    | ~ m1_pre_topc(X0_54,sK5)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | ~ v2_struct_0(sK3(sK5,X0_54,X1_54))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_8404])).

cnf(c_9619,plain,
    ( r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v2_struct_0(sK3(sK5,sK6,sK7))
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_9432])).

cnf(c_9620,plain,
    ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9619])).

cnf(c_20,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK3(X0,X1,X2))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8405,plain,
    ( r3_tsep_1(X0_54,X1_54,X2_54)
    | ~ r1_tsep_1(X1_54,X2_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X0_54)
    | v2_pre_topc(sK3(X0_54,X1_54,X2_54))
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_9433,plain,
    ( r3_tsep_1(sK5,X0_54,X1_54)
    | ~ r1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,sK5)
    | ~ m1_pre_topc(X0_54,sK5)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | v2_pre_topc(sK3(sK5,X0_54,X1_54))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_8405])).

cnf(c_9624,plain,
    ( r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | v2_pre_topc(sK3(sK5,sK6,sK7))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_9433])).

cnf(c_9625,plain,
    ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9624])).

cnf(c_19,plain,
    ( r3_tsep_1(X0,X1,X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8406,plain,
    ( r3_tsep_1(X0_54,X1_54,X2_54)
    | ~ r1_tsep_1(X1_54,X2_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK3(X0_54,X1_54,X2_54)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_9434,plain,
    ( r3_tsep_1(sK5,X0_54,X1_54)
    | ~ r1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,sK5)
    | ~ m1_pre_topc(X0_54,sK5)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | l1_pre_topc(sK3(sK5,X0_54,X1_54))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_8406])).

cnf(c_9714,plain,
    ( r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | l1_pre_topc(sK3(sK5,sK6,sK7))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_9434])).

cnf(c_9715,plain,
    ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9714])).

cnf(c_24,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8401,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_12165,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_8401])).

cnf(c_12166,plain,
    ( m1_pre_topc(sK5,sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12165])).

cnf(c_13579,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12743,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9620,c_9625,c_9715,c_12166])).

cnf(c_9341,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8401])).

cnf(c_36,plain,
    ( sP1(X0,X1,X2,X3)
    | v1_funct_1(sK4(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_8390,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_1(sK4(X0_54,X1_54,X2_54,X3_54)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_9352,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_1(sK4(X0_54,X1_54,X2_54,X3_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8390])).

cnf(c_35,plain,
    ( sP1(X0,X1,X2,X3)
    | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8391,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_2(sK4(X0_54,X1_54,X2_54,X3_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_9351,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_2(sK4(X0_54,X1_54,X2_54,X3_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8391])).

cnf(c_34,plain,
    ( sP1(X0,X1,X2,X3)
    | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8392,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | m1_subset_1(sK4(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_9350,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | m1_subset_1(sK4(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8392])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_8421,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X2_54,X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_9321,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
    | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8421])).

cnf(c_10519,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X4_54)
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | v1_funct_2(sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9350,c_9321])).

cnf(c_13378,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X4_54)
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9351,c_10519])).

cnf(c_13672,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X4_54)
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9352,c_13378])).

cnf(c_13778,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X0_54)
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9341,c_13672])).

cnf(c_3561,plain,
    ( r1_tsep_1(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3559,c_54,c_53,c_52,c_51,c_50,c_49,c_48])).

cnf(c_41,negated_conjecture,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3659,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ r3_tsep_1(sK5,sK6,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3561,c_41])).

cnf(c_8376,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ r3_tsep_1(sK5,sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_3659])).

cnf(c_9365,plain,
    ( sP1(sK8,sK5,sK7,sK6) != iProver_top
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8376])).

cnf(c_14347,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13778,c_9365])).

cnf(c_44,negated_conjecture,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_66,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_67,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_68,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_14496,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14347,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560])).

cnf(c_14502,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_13579,c_14496])).

cnf(c_11066,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_2(sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_9321])).

cnf(c_11074,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11066,c_55,c_56,c_57,c_10527])).

cnf(c_11075,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11074])).

cnf(c_11080,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(X1_54,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9333,c_11075])).

cnf(c_11346,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),sK7)
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9355,c_11080])).

cnf(c_12745,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11346,c_9335])).

cnf(c_13113,plain,
    ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12745,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9620,c_9625,c_9715])).

cnf(c_13114,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_13113])).

cnf(c_14504,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_13114,c_14496])).

cnf(c_16362,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_14502,c_14504])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8419,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_9323,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8419])).

cnf(c_10571,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_54)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9323])).

cnf(c_27808,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16362,c_10571])).

cnf(c_9431,plain,
    ( ~ sP0(sK3(sK5,X0_54,X1_54),X1_54,X0_54,sK5)
    | r3_tsep_1(sK5,X0_54,X1_54)
    | ~ r1_tsep_1(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,sK5)
    | ~ m1_pre_topc(X0_54,sK5)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_8407])).

cnf(c_9719,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_9431])).

cnf(c_9720,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9719])).

cnf(c_27906,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27808,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_9720,c_14347])).

cnf(c_38,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | v5_pre_topc(X4,X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
    | ~ v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X0,X4,X3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8389,plain,
    ( ~ sP1(X0_54,X1_54,X2_54,X3_54)
    | v5_pre_topc(X0_55,X1_54,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),X2_54,X0_54)
    | ~ v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),X3_54,X0_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54))
    | ~ v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54)) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_9353,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54) != iProver_top
    | v5_pre_topc(X0_55,X1_54,X0_54) = iProver_top
    | v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),X2_54,X0_54) != iProver_top
    | v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),X3_54,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8389])).

cnf(c_27910,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP1(sK3(sK5,sK6,sK7),sK5,sK7,X0_54) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27906,c_9353])).

cnf(c_45,negated_conjecture,
    ( sP1(X0,sK5,sK7,sK6)
    | r3_tsep_1(sK5,sK6,sK7)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8388,negated_conjecture,
    ( sP1(X0_54,sK5,sK7,sK6)
    | r3_tsep_1(sK5,sK6,sK7)
    | v2_struct_0(X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_10083,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6)
    | r3_tsep_1(sK5,sK6,sK7)
    | v2_struct_0(sK3(sK5,sK6,sK7))
    | ~ v2_pre_topc(sK3(sK5,sK6,sK7))
    | ~ l1_pre_topc(sK3(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_8388])).

cnf(c_10084,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) = iProver_top
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10083])).

cnf(c_10154,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_8409])).

cnf(c_10155,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10154])).

cnf(c_6,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8416,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_9326,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8416])).

cnf(c_10705,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9326])).

cnf(c_27809,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16362,c_10705])).

cnf(c_27816,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27809,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_9720,c_14347])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8418,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9324,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),X1_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8418])).

cnf(c_11154,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5)),sK7,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9324])).

cnf(c_27807,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16362,c_11154])).

cnf(c_27858,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27807,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_9720,c_14347])).

cnf(c_5,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8417,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_9325,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8417])).

cnf(c_11519,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9325])).

cnf(c_27806,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16362,c_11519])).

cnf(c_27863,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27806,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_9720,c_14347])).

cnf(c_27914,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27910])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
    | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0)
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4))
    | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8408,plain,
    ( ~ sP0(X0_54,X1_54,X2_54,X3_54)
    | v5_pre_topc(X0_55,k1_tsep_1(X3_54,X2_54,X1_54),X0_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),X1_54,X0_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),X2_54,X0_54)
    | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),u1_struct_0(X2_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_9334,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) != iProver_top
    | v5_pre_topc(X0_55,k1_tsep_1(X3_54,X2_54,X1_54),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),X2_54,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8408])).

cnf(c_10488,plain,
    ( sP0(X0_54,sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(X0_55,k1_tsep_1(sK5,sK6,sK7),X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55),sK6,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK7,X0_55),sK7,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK7,X0_55),u1_struct_0(sK7),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK7,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9334])).

cnf(c_10489,plain,
    ( sP0(X0_54,sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(X0_55,sK5,X0_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55),sK6,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),sK7,X0_54) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),u1_struct_0(sK7),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10488,c_8387])).

cnf(c_27805,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16362,c_10489])).

cnf(c_27923,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27805,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_9720,c_14347])).

cnf(c_8384,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(subtyping,[status(esa)],[c_50])).

cnf(c_9357,plain,
    ( m1_pre_topc(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8384])).

cnf(c_11419,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(X1_54,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(sK6,X1_54) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9357,c_11298])).

cnf(c_11510,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9357,c_11419])).

cnf(c_11778,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11510,c_55,c_56,c_57])).

cnf(c_11779,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_11778])).

cnf(c_12742,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11779,c_9335])).

cnf(c_13445,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12742,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9620,c_9625,c_9715,c_12166])).

cnf(c_14503,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_13445,c_14496])).

cnf(c_11347,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),sK6)
    | sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9357,c_11080])).

cnf(c_12744,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11347,c_9335])).

cnf(c_12873,plain,
    ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12744,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9620,c_9625,c_9715])).

cnf(c_12874,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_12873])).

cnf(c_14505,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_12874,c_14496])).

cnf(c_16512,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_14503,c_14505])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8412,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_9330,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8412])).

cnf(c_10759,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9330])).

cnf(c_28183,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16512,c_10759])).

cnf(c_28258,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28183,c_27923])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,X3)
    | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8414,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_9328,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),X2_54,X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8414])).

cnf(c_11226,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5)),sK6,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9328])).

cnf(c_28182,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16512,c_11226])).

cnf(c_28263,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28182,c_27923])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2,X3)
    | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8413,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X2_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_9329,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X2_54),u1_struct_0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8413])).

cnf(c_11651,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9329])).

cnf(c_28181,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16512,c_11651])).

cnf(c_28354,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28181,c_27923])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2,X3)
    | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8415,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_9327,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8415])).

cnf(c_12295,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9327])).

cnf(c_28180,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16512,c_12295])).

cnf(c_28359,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28180,c_27923])).

cnf(c_32688,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27910,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_9620,c_9625,c_9715,c_10084,c_10155,c_14347,c_27816,c_27858,c_27863,c_27914,c_27923,c_28180,c_28181,c_28182,c_28183])).

cnf(c_32692,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_32688])).

cnf(c_32841,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32692,c_27923])).

cnf(c_32845,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10527,c_32841])).

cnf(c_32848,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32845,c_27923])).

cnf(c_2,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | ~ v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
    | ~ v1_funct_1(sK2(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_325,plain,
    ( ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
    | sP0(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_13,c_12,c_11])).

cnf(c_326,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_8378,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | ~ v5_pre_topc(sK2(X0_54,X1_54,X2_54,X3_54),k1_tsep_1(X3_54,X2_54,X1_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_9363,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | v5_pre_topc(sK2(X0_54,X1_54,X2_54,X3_54),k1_tsep_1(X3_54,X2_54,X1_54),X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8378])).

cnf(c_10295,plain,
    ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(X0_54,sK7,sK6,sK5),sK5,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_8387,c_9363])).

cnf(c_32852,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_32848,c_10295])).

cnf(c_32919,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32852,c_27923])).

cnf(c_10518,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X5_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | v1_funct_2(sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | m1_pre_topc(X4_54,X5_54) != iProver_top
    | m1_pre_topc(X0_54,X5_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X5_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X5_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X5_54) != iProver_top
    | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9350,c_9322])).

cnf(c_13274,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X5_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | m1_pre_topc(X4_54,X5_54) != iProver_top
    | m1_pre_topc(X0_54,X5_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X5_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X5_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X5_54) != iProver_top
    | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9351,c_10518])).

cnf(c_15381,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X5_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | m1_pre_topc(X4_54,X5_54) != iProver_top
    | m1_pre_topc(X0_54,X5_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X5_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X5_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X5_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9352,c_13274])).

cnf(c_15397,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X4_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,X4_54) != iProver_top
    | m1_pre_topc(X4_54,X0_54) != iProver_top
    | v2_struct_0(X4_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X4_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X4_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9341,c_15381])).

cnf(c_15776,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k3_tmap_1(X0_54,X1_54,X0_54,X0_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_9341,c_15397])).

cnf(c_8500,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8401])).

cnf(c_16002,plain,
    ( sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k3_tmap_1(X0_54,X1_54,X0_54,X0_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15776,c_8500])).

cnf(c_16003,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k3_tmap_1(X0_54,X1_54,X0_54,X0_54,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_16002])).

cnf(c_16008,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6))
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_16003,c_9365])).

cnf(c_16219,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6))
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16008,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560])).

cnf(c_16227,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13579,c_16219])).

cnf(c_32963,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(demodulation,[status(thm)],[c_32919,c_16227])).

cnf(c_16229,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13114,c_16219])).

cnf(c_32965,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
    inference(demodulation,[status(thm)],[c_32919,c_16229])).

cnf(c_33463,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
    inference(superposition,[status(thm)],[c_32963,c_32965])).

cnf(c_42280,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33463,c_10489])).

cnf(c_3524,plain,
    ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
    | ~ r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK8)
    | sK6 != X1
    | sK7 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_42])).

cnf(c_3525,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_3524])).

cnf(c_3527,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | l1_pre_topc(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3525,c_54,c_53,c_52,c_51,c_50,c_49,c_48])).

cnf(c_3528,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | l1_pre_topc(sK8) ),
    inference(renaming,[status(thm)],[c_3527])).

cnf(c_3587,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | l1_pre_topc(sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3561,c_3528])).

cnf(c_3588,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3587])).

cnf(c_3507,plain,
    ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
    | ~ r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK8)
    | ~ l1_pre_topc(X0)
    | sK6 != X1
    | sK7 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_43])).

cnf(c_3508,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_3507])).

cnf(c_3510,plain,
    ( v2_pre_topc(sK8)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3508,c_54,c_53,c_52,c_51,c_50,c_49,c_48])).

cnf(c_3511,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | v2_pre_topc(sK8) ),
    inference(renaming,[status(thm)],[c_3510])).

cnf(c_3586,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | v2_pre_topc(sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3561,c_3511])).

cnf(c_3589,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3586])).

cnf(c_3490,plain,
    ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
    | ~ r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(sK8)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X1
    | sK7 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_44])).

cnf(c_3491,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_struct_0(sK8)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_3490])).

cnf(c_3493,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ v2_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3491,c_54,c_53,c_52,c_51,c_50,c_49,c_48])).

cnf(c_3494,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ v2_struct_0(sK8) ),
    inference(renaming,[status(thm)],[c_3493])).

cnf(c_3585,plain,
    ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ v2_struct_0(sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3561,c_3494])).

cnf(c_3590,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3585])).

cnf(c_3541,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
    | ~ r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X1
    | sK7 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_41])).

cnf(c_3542,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_3541])).

cnf(c_3544,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ sP1(sK8,sK5,sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3542,c_54,c_53,c_52,c_51,c_50,c_49,c_48])).

cnf(c_3545,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(renaming,[status(thm)],[c_3544])).

cnf(c_3575,plain,
    ( ~ sP1(sK8,sK5,sK7,sK6)
    | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3561,c_3545])).

cnf(c_3600,plain,
    ( sP1(sK8,sK5,sK7,sK6) != iProver_top
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3575])).

cnf(c_9673,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_8390])).

cnf(c_9674,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9673])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
    | ~ v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ v1_funct_1(sK4(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_299,plain,
    ( ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
    | sP1(X0,X1,X2,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_36,c_35,c_34])).

cnf(c_300,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_8379,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | ~ v5_pre_topc(sK4(X0_54,X1_54,X2_54,X3_54),X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_300])).

cnf(c_9672,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | ~ v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) ),
    inference(instantiation,[status(thm)],[c_8379])).

cnf(c_9676,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9672])).

cnf(c_29,plain,
    ( sP1(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8397,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_9671,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_8397])).

cnf(c_9678,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9671])).

cnf(c_33,plain,
    ( sP1(X0,X1,X2,X3)
    | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8393,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_9670,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) ),
    inference(instantiation,[status(thm)],[c_8393])).

cnf(c_9680,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9670])).

cnf(c_9669,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8391])).

cnf(c_9682,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9669])).

cnf(c_27,plain,
    ( sP1(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_8399,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54),X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_9668,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_8399])).

cnf(c_9684,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9668])).

cnf(c_31,plain,
    ( sP1(X0,X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8395,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v5_pre_topc(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54),X3_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_9667,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_8395])).

cnf(c_9686,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9667])).

cnf(c_9666,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) ),
    inference(instantiation,[status(thm)],[c_8392])).

cnf(c_9688,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9666])).

cnf(c_28,plain,
    ( sP1(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8398,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_2(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54),u1_struct_0(X2_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_9665,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8398])).

cnf(c_9690,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9665])).

cnf(c_32,plain,
    ( sP1(X0,X1,X2,X3)
    | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8394,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | v1_funct_2(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_9664,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_8394])).

cnf(c_9692,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9664])).

cnf(c_26,plain,
    ( sP1(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8400,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | m1_subset_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_9663,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) ),
    inference(instantiation,[status(thm)],[c_8400])).

cnf(c_9694,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9663])).

cnf(c_30,plain,
    ( sP1(X0,X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8396,plain,
    ( sP1(X0_54,X1_54,X2_54,X3_54)
    | m1_subset_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_9662,plain,
    ( sP1(sK8,sK5,sK7,sK6)
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) ),
    inference(instantiation,[status(thm)],[c_8396])).

cnf(c_9696,plain,
    ( sP1(sK8,sK5,sK7,sK6) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9662])).

cnf(c_22,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ r3_tsep_1(X3,X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8403,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54)
    | ~ r3_tsep_1(X3_54,X2_54,X1_54)
    | ~ m1_pre_topc(X1_54,X3_54)
    | ~ m1_pre_topc(X2_54,X3_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X3_54) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_12825,plain,
    ( sP0(sK8,sK7,sK6,sK5)
    | ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | v2_struct_0(sK8)
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_8403])).

cnf(c_12862,plain,
    ( sP0(sK8,sK7,sK6,sK5) = iProver_top
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12825])).

cnf(c_13777,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK6)
    | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9357,c_13672])).

cnf(c_13887,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK6)
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13777,c_55,c_56,c_57])).

cnf(c_13888,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK6)
    | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_13887])).

cnf(c_13893,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13888,c_9365])).

cnf(c_14173,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13893,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560])).

cnf(c_14174,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14173])).

cnf(c_14177,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_13579,c_14174])).

cnf(c_14179,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_13114,c_14174])).

cnf(c_15957,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_14177,c_14179])).

cnf(c_26512,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15957,c_10571])).

cnf(c_26717,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26512,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_14174])).

cnf(c_26721,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP1(sK3(sK5,sK6,sK7),sK5,sK7,X0_54) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26717,c_9353])).

cnf(c_26513,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15957,c_10705])).

cnf(c_26607,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26513,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_14174])).

cnf(c_26511,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15957,c_11154])).

cnf(c_26662,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26511,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_14174])).

cnf(c_26510,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15957,c_11519])).

cnf(c_26667,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26510,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_14174])).

cnf(c_26725,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_26721])).

cnf(c_26509,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15957,c_10489])).

cnf(c_26734,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26509,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_14174])).

cnf(c_14178,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_13445,c_14174])).

cnf(c_14180,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_12874,c_14174])).

cnf(c_16357,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_14178,c_14180])).

cnf(c_27378,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16357,c_12295])).

cnf(c_27379,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16357,c_11651])).

cnf(c_27380,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16357,c_11226])).

cnf(c_27381,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16357,c_10759])).

cnf(c_30849,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26721,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9620,c_9625,c_9715,c_10084,c_10155,c_14174,c_20956,c_26607,c_26662,c_26667,c_26717,c_26734,c_27378,c_27379,c_27380,c_27381])).

cnf(c_30853,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_30849])).

cnf(c_30895,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30853,c_26734])).

cnf(c_30899,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10527,c_30895])).

cnf(c_30902,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30899,c_26734])).

cnf(c_30906,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_30902,c_10295])).

cnf(c_30935,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30906,c_26734])).

cnf(c_15396,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK6)) = k3_tmap_1(sK5,X1_54,X0_54,sK6,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(sK6,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9357,c_15381])).

cnf(c_15429,plain,
    ( l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK6,X0_54) != iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK6)) = k3_tmap_1(sK5,X1_54,X0_54,sK6,sK4(X1_54,X0_54,X2_54,X3_54))
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15396,c_55,c_56,c_57])).

cnf(c_15430,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK6)) = k3_tmap_1(sK5,X1_54,X0_54,sK6,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(sK6,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_15429])).

cnf(c_15435,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15430,c_9365])).

cnf(c_15499,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15435,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_12166])).

cnf(c_15500,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_15499])).

cnf(c_15507,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13579,c_15500])).

cnf(c_30975,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(demodulation,[status(thm)],[c_30935,c_15507])).

cnf(c_15509,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13114,c_15500])).

cnf(c_30977,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
    inference(demodulation,[status(thm)],[c_30935,c_15509])).

cnf(c_31659,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_30975,c_30977])).

cnf(c_40666,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31659,c_10489])).

cnf(c_8423,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_9890,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_8423])).

cnf(c_10152,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_8410])).

cnf(c_10159,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10152])).

cnf(c_8428,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_9780,plain,
    ( X0_54 != X1_54
    | sK5 != X1_54
    | sK5 = X0_54 ),
    inference(instantiation,[status(thm)],[c_8428])).

cnf(c_10276,plain,
    ( X0_54 != sK5
    | sK5 = X0_54
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_9780])).

cnf(c_10561,plain,
    ( k1_tsep_1(sK5,sK6,sK7) != sK5
    | sK5 = k1_tsep_1(sK5,sK6,sK7)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_10276])).

cnf(c_8425,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_17087,plain,
    ( u1_struct_0(sK3(sK5,sK6,sK7)) = u1_struct_0(sK3(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_8425])).

cnf(c_8431,plain,
    ( u1_struct_0(X0_54) = u1_struct_0(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_13180,plain,
    ( u1_struct_0(sK5) = u1_struct_0(X0_54)
    | sK5 != X0_54 ),
    inference(instantiation,[status(thm)],[c_8431])).

cnf(c_18315,plain,
    ( u1_struct_0(sK5) = u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | sK5 != k1_tsep_1(sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_13180])).

cnf(c_14158,plain,
    ( ~ sP1(sK3(sK5,sK6,sK7),sK5,X0_54,X1_54)
    | v5_pre_topc(X0_55,sK5,sK3(sK5,sK6,sK7))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54),X0_54,sK3(sK5,sK6,sK7))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54),X1_54,sK3(sK5,sK6,sK7))
    | ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54)) ),
    inference(instantiation,[status(thm)],[c_8389])).

cnf(c_15475,plain,
    ( ~ sP1(sK3(sK5,sK6,sK7),sK5,X0_54,X1_54)
    | v5_pre_topc(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),sK5,sK3(sK5,sK6,sK7))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54),X1_54,sK3(sK5,sK6,sK7))
    | ~ v1_funct_2(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54),u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ m1_subset_1(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ v1_funct_1(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54)) ),
    inference(instantiation,[status(thm)],[c_14158])).

cnf(c_20953,plain,
    ( ~ sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6)
    | v5_pre_topc(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK5,sK3(sK5,sK6,sK7))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),sK6,sK3(sK5,sK6,sK7))
    | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),sK7,sK3(sK5,sK6,sK7))
    | ~ v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7)))
    | ~ m1_subset_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7)))))
    | ~ v1_funct_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6))
    | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7)) ),
    inference(instantiation,[status(thm)],[c_15475])).

cnf(c_20954,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20953])).

cnf(c_20956,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20954])).

cnf(c_8424,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_28192,plain,
    ( sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_8424])).

cnf(c_30978,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30935,c_15500])).

cnf(c_8437,plain,
    ( ~ v1_funct_2(X0_55,X0_56,X1_56)
    | v1_funct_2(X1_55,X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_13125,plain,
    ( ~ v1_funct_2(X0_55,X0_56,X1_56)
    | v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X1_54,sK7)))
    | u1_struct_0(sK3(sK5,X1_54,sK7)) != X1_56
    | u1_struct_0(sK5) != X0_56
    | sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5) != X0_55 ),
    inference(instantiation,[status(thm)],[c_8437])).

cnf(c_17409,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),X0_56)
    | v1_funct_2(sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X2_54,sK7)))
    | u1_struct_0(sK3(sK5,X2_54,sK7)) != X0_56
    | u1_struct_0(sK5) != u1_struct_0(X0_54)
    | sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5) != X0_55 ),
    inference(instantiation,[status(thm)],[c_13125])).

cnf(c_26334,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),X0_56)
    | v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X1_54,sK7)))
    | u1_struct_0(sK3(sK5,X1_54,sK7)) != X0_56
    | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5) != X0_55 ),
    inference(instantiation,[status(thm)],[c_17409])).

cnf(c_33466,plain,
    ( v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X1_54,sK7)))
    | ~ v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7)))
    | u1_struct_0(sK3(sK5,X1_54,sK7)) != u1_struct_0(sK3(sK5,sK6,sK7))
    | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5) != sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_26334])).

cnf(c_33467,plain,
    ( u1_struct_0(sK3(sK5,X0_54,sK7)) != u1_struct_0(sK3(sK5,sK6,sK7))
    | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5) != sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | v1_funct_2(sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X0_54,sK7))) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33466])).

cnf(c_33469,plain,
    ( u1_struct_0(sK3(sK5,sK6,sK7)) != u1_struct_0(sK3(sK5,sK6,sK7))
    | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33467])).

cnf(c_15508,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13445,c_15500])).

cnf(c_30974,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(demodulation,[status(thm)],[c_30935,c_15508])).

cnf(c_15510,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_12874,c_15500])).

cnf(c_30976,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
    inference(demodulation,[status(thm)],[c_30935,c_15510])).

cnf(c_31190,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_30974,c_30976])).

cnf(c_39494,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31190,c_10759])).

cnf(c_39513,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39494,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_39493,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31190,c_11226])).

cnf(c_39519,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39493,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_39492,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31190,c_11651])).

cnf(c_39560,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39492,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_39491,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31190,c_12295])).

cnf(c_39565,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39491,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_40670,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31659,c_10705])).

cnf(c_40677,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40670,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_40668,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31659,c_11154])).

cnf(c_40708,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40668,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_40667,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31659,c_11519])).

cnf(c_40713,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40667,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_40669,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31659,c_10571])).

cnf(c_40739,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40669,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_40840,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40666,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_8387,c_9620,c_9625,c_9715,c_9720,c_9890,c_10084,c_10155,c_10159,c_10561,c_17087,c_18315,c_20956,c_28192,c_30978,c_33469,c_39513,c_39519,c_39560,c_39565,c_40677,c_40708,c_40713,c_40739])).

cnf(c_40844,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_40840])).

cnf(c_40926,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40844,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_40930,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_40926,c_10295])).

cnf(c_40933,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40930,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_30978])).

cnf(c_13776,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK7)
    | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9355,c_13672])).

cnf(c_13789,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK7)
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13776,c_55,c_56,c_57])).

cnf(c_13790,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK7)
    | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_13789])).

cnf(c_13795,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13790,c_9365])).

cnf(c_13896,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13795,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560])).

cnf(c_13897,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_13896])).

cnf(c_13900,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_13579,c_13897])).

cnf(c_13902,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_13114,c_13897])).

cnf(c_15921,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_13900,c_13902])).

cnf(c_25681,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15921,c_10571])).

cnf(c_25855,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25681,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_13897])).

cnf(c_25859,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP1(sK3(sK5,sK6,sK7),sK5,sK7,X0_54) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25855,c_9353])).

cnf(c_25682,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15921,c_10705])).

cnf(c_25777,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25682,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_13897])).

cnf(c_25680,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15921,c_11154])).

cnf(c_25782,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25680,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_13897])).

cnf(c_25679,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15921,c_11519])).

cnf(c_25850,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25679,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_13897])).

cnf(c_25863,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25859])).

cnf(c_25678,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15921,c_10489])).

cnf(c_25934,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25678,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_13897])).

cnf(c_13901,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_13445,c_13897])).

cnf(c_13903,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_12874,c_13897])).

cnf(c_15952,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_13901,c_13903])).

cnf(c_26137,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15952,c_12295])).

cnf(c_26138,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15952,c_11651])).

cnf(c_26139,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15952,c_11226])).

cnf(c_26140,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15952,c_10759])).

cnf(c_26394,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25859,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9620,c_9625,c_9715,c_10084,c_10155,c_13897,c_25777,c_25782,c_25850,c_25863,c_25934,c_26137,c_26138,c_26139,c_26140])).

cnf(c_26398,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_26394])).

cnf(c_26401,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26398,c_25934])).

cnf(c_26405,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10527,c_26401])).

cnf(c_26503,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26405,c_25934])).

cnf(c_26507,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_26503,c_10295])).

cnf(c_26560,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26507,c_25934])).

cnf(c_15395,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK7)) = k3_tmap_1(sK5,X1_54,X0_54,sK7,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(sK7,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9355,c_15381])).

cnf(c_15406,plain,
    ( l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK7,X0_54) != iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK7)) = k3_tmap_1(sK5,X1_54,X0_54,sK7,sK4(X1_54,X0_54,X2_54,X3_54))
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15395,c_55,c_56,c_57])).

cnf(c_15407,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK7)) = k3_tmap_1(sK5,X1_54,X0_54,sK7,sK4(X1_54,X0_54,X2_54,X3_54))
    | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
    | m1_pre_topc(X0_54,sK5) != iProver_top
    | m1_pre_topc(sK7,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_15406])).

cnf(c_15412,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6))
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15407,c_9365])).

cnf(c_15482,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15412,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_3560,c_12166])).

cnf(c_15483,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6))
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_15482])).

cnf(c_15490,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13579,c_15483])).

cnf(c_26593,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(demodulation,[status(thm)],[c_26560,c_15490])).

cnf(c_15492,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13114,c_15483])).

cnf(c_26595,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
    inference(demodulation,[status(thm)],[c_26560,c_15492])).

cnf(c_27549,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_26593,c_26595])).

cnf(c_38864,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27549,c_10489])).

cnf(c_26596,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26560,c_15483])).

cnf(c_15491,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_13445,c_15483])).

cnf(c_26592,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(demodulation,[status(thm)],[c_26560,c_15491])).

cnf(c_15493,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_12874,c_15483])).

cnf(c_26594,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
    inference(demodulation,[status(thm)],[c_26560,c_15493])).

cnf(c_26982,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_26592,c_26594])).

cnf(c_36249,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26982,c_10759])).

cnf(c_36373,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36249,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_36248,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26982,c_11226])).

cnf(c_36378,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36248,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_36247,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26982,c_11651])).

cnf(c_36477,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36247,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_36246,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26982,c_12295])).

cnf(c_36482,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36246,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_38868,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27549,c_10705])).

cnf(c_38946,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38868,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_38866,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27549,c_11154])).

cnf(c_38951,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38866,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_38865,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27549,c_11519])).

cnf(c_39027,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38865,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_38867,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27549,c_10571])).

cnf(c_39032,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38867,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_39092,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38864,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_8387,c_9620,c_9625,c_9715,c_9720,c_9890,c_10084,c_10155,c_10159,c_10561,c_17087,c_18315,c_20956,c_26596,c_28192,c_33469,c_36373,c_36378,c_36477,c_36482,c_38946,c_38951,c_39027,c_39032])).

cnf(c_39096,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_39092])).

cnf(c_39099,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39096,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_39103,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
    | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_39099,c_10295])).

cnf(c_39196,plain,
    ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39103,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_9720,c_26596])).

cnf(c_39198,plain,
    ( sP0(sK8,sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),sK6,sK8) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)),sK7,sK8) != iProver_top
    | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),u1_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6))) != iProver_top
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_39196,c_10489])).

cnf(c_39199,plain,
    ( sP0(sK8,sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),sK6,sK8) != iProver_top
    | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),u1_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))) != iProver_top
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39198,c_39196])).

cnf(c_40935,plain,
    ( sP0(sK8,sK7,sK6,sK5) != iProver_top
    | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) != iProver_top
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) != iProver_top
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_40933,c_39199])).

cnf(c_42579,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42280,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,c_9720,c_12862,c_40935])).

cnf(c_42597,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11504,c_42579])).

cnf(c_9339,plain,
    ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
    | r3_tsep_1(X3_54,X2_54,X1_54) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8403])).

cnf(c_42583,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | m1_pre_topc(sK6,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9339,c_42579])).

cnf(c_1641,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
    | ~ r1_tsep_1(sK6,sK7)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_300,c_41])).

cnf(c_1642,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8)
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_1641])).

cnf(c_1643,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_1654,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v1_funct_1(sK4(X0,X1,X2,X3))
    | sK6 != X3
    | sK7 != X2
    | sK5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_41])).

cnf(c_1655,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) ),
    inference(unflattening,[status(thm)],[c_1654])).

cnf(c_1656,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_1667,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
    | ~ r1_tsep_1(sK6,sK7)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_41])).

cnf(c_1668,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8))
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_1667])).

cnf(c_1669,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_1680,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | sK6 != X3
    | sK7 != X2
    | sK5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_41])).

cnf(c_1681,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_1680])).

cnf(c_1682,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_1693,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v1_funct_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3))
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_1694,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) ),
    inference(unflattening,[status(thm)],[c_1693])).

cnf(c_1695,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1694])).

cnf(c_1706,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v1_funct_2(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X1))
    | ~ r1_tsep_1(sK6,sK7)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_41])).

cnf(c_1707,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8))
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_1706])).

cnf(c_1708,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1707])).

cnf(c_1719,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v5_pre_topc(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3),X3,X1)
    | ~ r1_tsep_1(sK6,sK7)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_41])).

cnf(c_1720,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8)
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_1719])).

cnf(c_1721,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1720])).

cnf(c_1732,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | m1_subset_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_1733,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_1732])).

cnf(c_1734,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1733])).

cnf(c_1745,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v1_funct_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2))
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_1746,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) ),
    inference(unflattening,[status(thm)],[c_1745])).

cnf(c_1747,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1746])).

cnf(c_1758,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v1_funct_2(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ r1_tsep_1(sK6,sK7)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_1759,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8))
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_1758])).

cnf(c_1760,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1771,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v5_pre_topc(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2),X2,X1)
    | ~ r1_tsep_1(sK6,sK7)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_1772,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8)
    | ~ r1_tsep_1(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_1771])).

cnf(c_1773,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) = iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_1784,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | m1_subset_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | sK6 != X3
    | sK7 != X2
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_41])).

cnf(c_1785,plain,
    ( ~ r3_tsep_1(sK5,sK6,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_1784])).

cnf(c_1786,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
    | r1_tsep_1(sK6,sK7) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_43087,plain,
    ( r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42583,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_12862,c_40935])).

cnf(c_44314,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42597,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_9620,c_9625,c_9715,c_12166,c_12743,c_12862,c_40935])).

cnf(c_42599,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11346,c_42579])).

cnf(c_42889,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42599,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_12862,c_13114,c_40935])).

cnf(c_44316,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
    inference(light_normalisation,[status(thm)],[c_44314,c_42889])).

cnf(c_44336,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_44316,c_10571])).

cnf(c_44485,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44336,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,c_9720,c_12862,c_40935])).

cnf(c_42596,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
    | m1_pre_topc(sK5,sK5) != iProver_top
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11779,c_42579])).

cnf(c_43315,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42596,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_9620,c_9625,c_9715,c_12166,c_12742,c_12862,c_40935])).

cnf(c_42598,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
    | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
    | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11347,c_42579])).

cnf(c_42839,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42598,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_12862,c_12874,c_40935])).

cnf(c_43317,plain,
    ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
    inference(light_normalisation,[status(thm)],[c_43315,c_42839])).

cnf(c_43337,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_43317,c_12295])).

cnf(c_43755,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43337,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,c_9720,c_12862,c_40935])).

cnf(c_43759,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK6,X0_54) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_43755,c_9353])).

cnf(c_43338,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_43317,c_11651])).

cnf(c_43339,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_43317,c_11226])).

cnf(c_43340,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_43317,c_10759])).

cnf(c_43771,plain,
    ( v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | sP1(sK3(sK5,sK6,sK7),sK5,sK6,X0_54) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43759,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_3588,c_3589,c_3590,c_3600,c_8387,c_9674,c_9676,c_9678,c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,c_9720,c_9890,c_10155,c_10159,c_10561,c_12862,c_17087,c_18315,c_28192,c_33469,c_40935,c_43338,c_43339,c_43340])).

cnf(c_43772,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK6,X0_54) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_43771])).

cnf(c_44492,plain,
    ( sP1(sK3(sK5,sK6,sK7),sK5,sK6,sK7) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_44485,c_43772])).

cnf(c_44334,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_44316,c_11519])).

cnf(c_44335,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_44316,c_11154])).

cnf(c_44337,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_44316,c_10705])).

cnf(c_44578,plain,
    ( m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44492,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_3588,c_3589,c_3590,c_3600,c_8387,c_9620,c_9625,c_9674,c_9676,c_9678,c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,c_9715,c_9720,c_9890,c_10084,c_10155,c_10159,c_10561,c_12862,c_17087,c_18315,c_20956,c_28192,c_33469,c_40935,c_43337,c_43338,c_43339,c_43340,c_44334,c_44335,c_44336,c_44337])).

cnf(c_44579,plain,
    ( v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
    | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_44578])).

cnf(c_44582,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
    | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10985,c_44579])).

cnf(c_44656,plain,
    ( v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44582,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,c_9720,c_12862,c_40935])).

cnf(c_44660,plain,
    ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_44656,c_10295])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44660,c_42579])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.47/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.47/3.00  
% 19.47/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.47/3.00  
% 19.47/3.00  ------  iProver source info
% 19.47/3.00  
% 19.47/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.47/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.47/3.00  git: non_committed_changes: false
% 19.47/3.00  git: last_make_outside_of_git: false
% 19.47/3.00  
% 19.47/3.00  ------ 
% 19.47/3.00  
% 19.47/3.00  ------ Input Options
% 19.47/3.00  
% 19.47/3.00  --out_options                           all
% 19.47/3.00  --tptp_safe_out                         true
% 19.47/3.00  --problem_path                          ""
% 19.47/3.00  --include_path                          ""
% 19.47/3.00  --clausifier                            res/vclausify_rel
% 19.47/3.00  --clausifier_options                    ""
% 19.47/3.00  --stdin                                 false
% 19.47/3.00  --stats_out                             all
% 19.47/3.00  
% 19.47/3.00  ------ General Options
% 19.47/3.00  
% 19.47/3.00  --fof                                   false
% 19.47/3.00  --time_out_real                         305.
% 19.47/3.00  --time_out_virtual                      -1.
% 19.47/3.00  --symbol_type_check                     false
% 19.47/3.00  --clausify_out                          false
% 19.47/3.00  --sig_cnt_out                           false
% 19.47/3.00  --trig_cnt_out                          false
% 19.47/3.00  --trig_cnt_out_tolerance                1.
% 19.47/3.00  --trig_cnt_out_sk_spl                   false
% 19.47/3.00  --abstr_cl_out                          false
% 19.47/3.00  
% 19.47/3.00  ------ Global Options
% 19.47/3.00  
% 19.47/3.00  --schedule                              default
% 19.47/3.00  --add_important_lit                     false
% 19.47/3.00  --prop_solver_per_cl                    1000
% 19.47/3.00  --min_unsat_core                        false
% 19.47/3.00  --soft_assumptions                      false
% 19.47/3.00  --soft_lemma_size                       3
% 19.47/3.00  --prop_impl_unit_size                   0
% 19.47/3.00  --prop_impl_unit                        []
% 19.47/3.00  --share_sel_clauses                     true
% 19.47/3.00  --reset_solvers                         false
% 19.47/3.00  --bc_imp_inh                            [conj_cone]
% 19.47/3.00  --conj_cone_tolerance                   3.
% 19.47/3.00  --extra_neg_conj                        none
% 19.47/3.00  --large_theory_mode                     true
% 19.47/3.00  --prolific_symb_bound                   200
% 19.47/3.00  --lt_threshold                          2000
% 19.47/3.00  --clause_weak_htbl                      true
% 19.47/3.00  --gc_record_bc_elim                     false
% 19.47/3.00  
% 19.47/3.00  ------ Preprocessing Options
% 19.47/3.00  
% 19.47/3.00  --preprocessing_flag                    true
% 19.47/3.00  --time_out_prep_mult                    0.1
% 19.47/3.00  --splitting_mode                        input
% 19.47/3.00  --splitting_grd                         true
% 19.47/3.00  --splitting_cvd                         false
% 19.47/3.00  --splitting_cvd_svl                     false
% 19.47/3.00  --splitting_nvd                         32
% 19.47/3.00  --sub_typing                            true
% 19.47/3.00  --prep_gs_sim                           true
% 19.47/3.00  --prep_unflatten                        true
% 19.47/3.00  --prep_res_sim                          true
% 19.47/3.00  --prep_upred                            true
% 19.47/3.00  --prep_sem_filter                       exhaustive
% 19.47/3.00  --prep_sem_filter_out                   false
% 19.47/3.00  --pred_elim                             true
% 19.47/3.00  --res_sim_input                         true
% 19.47/3.00  --eq_ax_congr_red                       true
% 19.47/3.00  --pure_diseq_elim                       true
% 19.47/3.00  --brand_transform                       false
% 19.47/3.00  --non_eq_to_eq                          false
% 19.47/3.00  --prep_def_merge                        true
% 19.47/3.00  --prep_def_merge_prop_impl              false
% 19.47/3.00  --prep_def_merge_mbd                    true
% 19.47/3.00  --prep_def_merge_tr_red                 false
% 19.47/3.00  --prep_def_merge_tr_cl                  false
% 19.47/3.00  --smt_preprocessing                     true
% 19.47/3.00  --smt_ac_axioms                         fast
% 19.47/3.00  --preprocessed_out                      false
% 19.47/3.00  --preprocessed_stats                    false
% 19.47/3.00  
% 19.47/3.00  ------ Abstraction refinement Options
% 19.47/3.00  
% 19.47/3.00  --abstr_ref                             []
% 19.47/3.00  --abstr_ref_prep                        false
% 19.47/3.00  --abstr_ref_until_sat                   false
% 19.47/3.00  --abstr_ref_sig_restrict                funpre
% 19.47/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.47/3.00  --abstr_ref_under                       []
% 19.47/3.00  
% 19.47/3.00  ------ SAT Options
% 19.47/3.00  
% 19.47/3.00  --sat_mode                              false
% 19.47/3.00  --sat_fm_restart_options                ""
% 19.47/3.00  --sat_gr_def                            false
% 19.47/3.00  --sat_epr_types                         true
% 19.47/3.00  --sat_non_cyclic_types                  false
% 19.47/3.00  --sat_finite_models                     false
% 19.47/3.00  --sat_fm_lemmas                         false
% 19.47/3.00  --sat_fm_prep                           false
% 19.47/3.00  --sat_fm_uc_incr                        true
% 19.47/3.00  --sat_out_model                         small
% 19.47/3.00  --sat_out_clauses                       false
% 19.47/3.00  
% 19.47/3.00  ------ QBF Options
% 19.47/3.00  
% 19.47/3.00  --qbf_mode                              false
% 19.47/3.00  --qbf_elim_univ                         false
% 19.47/3.00  --qbf_dom_inst                          none
% 19.47/3.00  --qbf_dom_pre_inst                      false
% 19.47/3.00  --qbf_sk_in                             false
% 19.47/3.00  --qbf_pred_elim                         true
% 19.47/3.00  --qbf_split                             512
% 19.47/3.00  
% 19.47/3.00  ------ BMC1 Options
% 19.47/3.00  
% 19.47/3.00  --bmc1_incremental                      false
% 19.47/3.00  --bmc1_axioms                           reachable_all
% 19.47/3.00  --bmc1_min_bound                        0
% 19.47/3.00  --bmc1_max_bound                        -1
% 19.47/3.00  --bmc1_max_bound_default                -1
% 19.47/3.00  --bmc1_symbol_reachability              true
% 19.47/3.00  --bmc1_property_lemmas                  false
% 19.47/3.00  --bmc1_k_induction                      false
% 19.47/3.00  --bmc1_non_equiv_states                 false
% 19.47/3.00  --bmc1_deadlock                         false
% 19.47/3.00  --bmc1_ucm                              false
% 19.47/3.00  --bmc1_add_unsat_core                   none
% 19.47/3.00  --bmc1_unsat_core_children              false
% 19.47/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.47/3.00  --bmc1_out_stat                         full
% 19.47/3.00  --bmc1_ground_init                      false
% 19.47/3.00  --bmc1_pre_inst_next_state              false
% 19.47/3.00  --bmc1_pre_inst_state                   false
% 19.47/3.00  --bmc1_pre_inst_reach_state             false
% 19.47/3.00  --bmc1_out_unsat_core                   false
% 19.47/3.00  --bmc1_aig_witness_out                  false
% 19.47/3.00  --bmc1_verbose                          false
% 19.47/3.00  --bmc1_dump_clauses_tptp                false
% 19.47/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.47/3.00  --bmc1_dump_file                        -
% 19.47/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.47/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.47/3.00  --bmc1_ucm_extend_mode                  1
% 19.47/3.00  --bmc1_ucm_init_mode                    2
% 19.47/3.00  --bmc1_ucm_cone_mode                    none
% 19.47/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.47/3.00  --bmc1_ucm_relax_model                  4
% 19.47/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.47/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.47/3.00  --bmc1_ucm_layered_model                none
% 19.47/3.00  --bmc1_ucm_max_lemma_size               10
% 19.47/3.00  
% 19.47/3.00  ------ AIG Options
% 19.47/3.00  
% 19.47/3.00  --aig_mode                              false
% 19.47/3.00  
% 19.47/3.00  ------ Instantiation Options
% 19.47/3.00  
% 19.47/3.00  --instantiation_flag                    true
% 19.47/3.00  --inst_sos_flag                         true
% 19.47/3.00  --inst_sos_phase                        true
% 19.47/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.47/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.47/3.00  --inst_lit_sel_side                     num_symb
% 19.47/3.00  --inst_solver_per_active                1400
% 19.47/3.00  --inst_solver_calls_frac                1.
% 19.47/3.00  --inst_passive_queue_type               priority_queues
% 19.47/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.47/3.00  --inst_passive_queues_freq              [25;2]
% 19.47/3.00  --inst_dismatching                      true
% 19.47/3.00  --inst_eager_unprocessed_to_passive     true
% 19.47/3.00  --inst_prop_sim_given                   true
% 19.47/3.00  --inst_prop_sim_new                     false
% 19.47/3.00  --inst_subs_new                         false
% 19.47/3.00  --inst_eq_res_simp                      false
% 19.47/3.00  --inst_subs_given                       false
% 19.47/3.00  --inst_orphan_elimination               true
% 19.47/3.00  --inst_learning_loop_flag               true
% 19.47/3.00  --inst_learning_start                   3000
% 19.47/3.00  --inst_learning_factor                  2
% 19.47/3.00  --inst_start_prop_sim_after_learn       3
% 19.47/3.00  --inst_sel_renew                        solver
% 19.47/3.00  --inst_lit_activity_flag                true
% 19.47/3.00  --inst_restr_to_given                   false
% 19.47/3.00  --inst_activity_threshold               500
% 19.47/3.00  --inst_out_proof                        true
% 19.47/3.00  
% 19.47/3.00  ------ Resolution Options
% 19.47/3.00  
% 19.47/3.00  --resolution_flag                       true
% 19.47/3.00  --res_lit_sel                           adaptive
% 19.47/3.00  --res_lit_sel_side                      none
% 19.47/3.00  --res_ordering                          kbo
% 19.47/3.00  --res_to_prop_solver                    active
% 19.47/3.00  --res_prop_simpl_new                    false
% 19.47/3.00  --res_prop_simpl_given                  true
% 19.47/3.00  --res_passive_queue_type                priority_queues
% 19.47/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.47/3.00  --res_passive_queues_freq               [15;5]
% 19.47/3.00  --res_forward_subs                      full
% 19.47/3.00  --res_backward_subs                     full
% 19.47/3.00  --res_forward_subs_resolution           true
% 19.47/3.00  --res_backward_subs_resolution          true
% 19.47/3.00  --res_orphan_elimination                true
% 19.47/3.00  --res_time_limit                        2.
% 19.47/3.00  --res_out_proof                         true
% 19.47/3.00  
% 19.47/3.00  ------ Superposition Options
% 19.47/3.00  
% 19.47/3.00  --superposition_flag                    true
% 19.47/3.00  --sup_passive_queue_type                priority_queues
% 19.47/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.47/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.47/3.00  --demod_completeness_check              fast
% 19.47/3.00  --demod_use_ground                      true
% 19.47/3.00  --sup_to_prop_solver                    passive
% 19.47/3.00  --sup_prop_simpl_new                    true
% 19.47/3.00  --sup_prop_simpl_given                  true
% 19.47/3.00  --sup_fun_splitting                     true
% 19.47/3.00  --sup_smt_interval                      50000
% 19.47/3.00  
% 19.47/3.00  ------ Superposition Simplification Setup
% 19.47/3.00  
% 19.47/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.47/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.47/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.47/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.47/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.47/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.47/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.47/3.00  --sup_immed_triv                        [TrivRules]
% 19.47/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.47/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.47/3.00  --sup_immed_bw_main                     []
% 19.47/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.47/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.47/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.47/3.00  --sup_input_bw                          []
% 19.47/3.00  
% 19.47/3.00  ------ Combination Options
% 19.47/3.00  
% 19.47/3.00  --comb_res_mult                         3
% 19.47/3.00  --comb_sup_mult                         2
% 19.47/3.00  --comb_inst_mult                        10
% 19.47/3.00  
% 19.47/3.00  ------ Debug Options
% 19.47/3.00  
% 19.47/3.00  --dbg_backtrace                         false
% 19.47/3.00  --dbg_dump_prop_clauses                 false
% 19.47/3.00  --dbg_dump_prop_clauses_file            -
% 19.47/3.00  --dbg_out_stat                          false
% 19.47/3.00  ------ Parsing...
% 19.47/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.47/3.00  
% 19.47/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.47/3.00  
% 19.47/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.47/3.00  
% 19.47/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.47/3.00  ------ Proving...
% 19.47/3.00  ------ Problem Properties 
% 19.47/3.00  
% 19.47/3.00  
% 19.47/3.00  clauses                                 49
% 19.47/3.00  conjectures                             9
% 19.47/3.00  EPR                                     16
% 19.47/3.00  Horn                                    18
% 19.47/3.00  unary                                   9
% 19.47/3.00  binary                                  29
% 19.47/3.00  lits                                    183
% 19.47/3.00  lits eq                                 3
% 19.47/3.00  fd_pure                                 0
% 19.47/3.00  fd_pseudo                               0
% 19.47/3.00  fd_cond                                 0
% 19.47/3.00  fd_pseudo_cond                          0
% 19.47/3.00  AC symbols                              0
% 19.47/3.00  
% 19.47/3.00  ------ Schedule dynamic 5 is on 
% 19.47/3.00  
% 19.47/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.47/3.00  
% 19.47/3.00  
% 19.47/3.00  ------ 
% 19.47/3.00  Current options:
% 19.47/3.00  ------ 
% 19.47/3.00  
% 19.47/3.00  ------ Input Options
% 19.47/3.00  
% 19.47/3.00  --out_options                           all
% 19.47/3.00  --tptp_safe_out                         true
% 19.47/3.00  --problem_path                          ""
% 19.47/3.00  --include_path                          ""
% 19.47/3.00  --clausifier                            res/vclausify_rel
% 19.47/3.00  --clausifier_options                    ""
% 19.47/3.00  --stdin                                 false
% 19.47/3.00  --stats_out                             all
% 19.47/3.00  
% 19.47/3.00  ------ General Options
% 19.47/3.00  
% 19.47/3.00  --fof                                   false
% 19.47/3.00  --time_out_real                         305.
% 19.47/3.00  --time_out_virtual                      -1.
% 19.47/3.00  --symbol_type_check                     false
% 19.47/3.00  --clausify_out                          false
% 19.47/3.00  --sig_cnt_out                           false
% 19.47/3.00  --trig_cnt_out                          false
% 19.47/3.00  --trig_cnt_out_tolerance                1.
% 19.47/3.00  --trig_cnt_out_sk_spl                   false
% 19.47/3.00  --abstr_cl_out                          false
% 19.47/3.00  
% 19.47/3.00  ------ Global Options
% 19.47/3.00  
% 19.47/3.00  --schedule                              default
% 19.47/3.00  --add_important_lit                     false
% 19.47/3.00  --prop_solver_per_cl                    1000
% 19.47/3.00  --min_unsat_core                        false
% 19.47/3.00  --soft_assumptions                      false
% 19.47/3.00  --soft_lemma_size                       3
% 19.47/3.00  --prop_impl_unit_size                   0
% 19.47/3.00  --prop_impl_unit                        []
% 19.47/3.00  --share_sel_clauses                     true
% 19.47/3.00  --reset_solvers                         false
% 19.47/3.00  --bc_imp_inh                            [conj_cone]
% 19.47/3.00  --conj_cone_tolerance                   3.
% 19.47/3.00  --extra_neg_conj                        none
% 19.47/3.00  --large_theory_mode                     true
% 19.47/3.00  --prolific_symb_bound                   200
% 19.47/3.00  --lt_threshold                          2000
% 19.47/3.00  --clause_weak_htbl                      true
% 19.47/3.00  --gc_record_bc_elim                     false
% 19.47/3.00  
% 19.47/3.00  ------ Preprocessing Options
% 19.47/3.00  
% 19.47/3.00  --preprocessing_flag                    true
% 19.47/3.00  --time_out_prep_mult                    0.1
% 19.47/3.00  --splitting_mode                        input
% 19.47/3.00  --splitting_grd                         true
% 19.47/3.00  --splitting_cvd                         false
% 19.47/3.00  --splitting_cvd_svl                     false
% 19.47/3.00  --splitting_nvd                         32
% 19.47/3.00  --sub_typing                            true
% 19.47/3.00  --prep_gs_sim                           true
% 19.47/3.00  --prep_unflatten                        true
% 19.47/3.00  --prep_res_sim                          true
% 19.47/3.00  --prep_upred                            true
% 19.47/3.00  --prep_sem_filter                       exhaustive
% 19.47/3.00  --prep_sem_filter_out                   false
% 19.47/3.00  --pred_elim                             true
% 19.47/3.00  --res_sim_input                         true
% 19.47/3.00  --eq_ax_congr_red                       true
% 19.47/3.00  --pure_diseq_elim                       true
% 19.47/3.00  --brand_transform                       false
% 19.47/3.00  --non_eq_to_eq                          false
% 19.47/3.00  --prep_def_merge                        true
% 19.47/3.00  --prep_def_merge_prop_impl              false
% 19.47/3.00  --prep_def_merge_mbd                    true
% 19.47/3.00  --prep_def_merge_tr_red                 false
% 19.47/3.00  --prep_def_merge_tr_cl                  false
% 19.47/3.00  --smt_preprocessing                     true
% 19.47/3.00  --smt_ac_axioms                         fast
% 19.47/3.00  --preprocessed_out                      false
% 19.47/3.00  --preprocessed_stats                    false
% 19.47/3.00  
% 19.47/3.00  ------ Abstraction refinement Options
% 19.47/3.00  
% 19.47/3.00  --abstr_ref                             []
% 19.47/3.00  --abstr_ref_prep                        false
% 19.47/3.00  --abstr_ref_until_sat                   false
% 19.47/3.00  --abstr_ref_sig_restrict                funpre
% 19.47/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.47/3.00  --abstr_ref_under                       []
% 19.47/3.00  
% 19.47/3.00  ------ SAT Options
% 19.47/3.00  
% 19.47/3.00  --sat_mode                              false
% 19.47/3.00  --sat_fm_restart_options                ""
% 19.47/3.00  --sat_gr_def                            false
% 19.47/3.00  --sat_epr_types                         true
% 19.47/3.00  --sat_non_cyclic_types                  false
% 19.47/3.00  --sat_finite_models                     false
% 19.47/3.00  --sat_fm_lemmas                         false
% 19.47/3.00  --sat_fm_prep                           false
% 19.47/3.00  --sat_fm_uc_incr                        true
% 19.47/3.00  --sat_out_model                         small
% 19.47/3.00  --sat_out_clauses                       false
% 19.47/3.00  
% 19.47/3.00  ------ QBF Options
% 19.47/3.00  
% 19.47/3.00  --qbf_mode                              false
% 19.47/3.00  --qbf_elim_univ                         false
% 19.47/3.00  --qbf_dom_inst                          none
% 19.47/3.00  --qbf_dom_pre_inst                      false
% 19.47/3.00  --qbf_sk_in                             false
% 19.47/3.00  --qbf_pred_elim                         true
% 19.47/3.00  --qbf_split                             512
% 19.47/3.00  
% 19.47/3.00  ------ BMC1 Options
% 19.47/3.00  
% 19.47/3.00  --bmc1_incremental                      false
% 19.47/3.00  --bmc1_axioms                           reachable_all
% 19.47/3.00  --bmc1_min_bound                        0
% 19.47/3.00  --bmc1_max_bound                        -1
% 19.47/3.00  --bmc1_max_bound_default                -1
% 19.47/3.00  --bmc1_symbol_reachability              true
% 19.47/3.00  --bmc1_property_lemmas                  false
% 19.47/3.00  --bmc1_k_induction                      false
% 19.47/3.00  --bmc1_non_equiv_states                 false
% 19.47/3.00  --bmc1_deadlock                         false
% 19.47/3.00  --bmc1_ucm                              false
% 19.47/3.00  --bmc1_add_unsat_core                   none
% 19.47/3.00  --bmc1_unsat_core_children              false
% 19.47/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.47/3.00  --bmc1_out_stat                         full
% 19.47/3.00  --bmc1_ground_init                      false
% 19.47/3.00  --bmc1_pre_inst_next_state              false
% 19.47/3.00  --bmc1_pre_inst_state                   false
% 19.47/3.00  --bmc1_pre_inst_reach_state             false
% 19.47/3.00  --bmc1_out_unsat_core                   false
% 19.47/3.00  --bmc1_aig_witness_out                  false
% 19.47/3.00  --bmc1_verbose                          false
% 19.47/3.00  --bmc1_dump_clauses_tptp                false
% 19.47/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.47/3.00  --bmc1_dump_file                        -
% 19.47/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.47/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.47/3.00  --bmc1_ucm_extend_mode                  1
% 19.47/3.00  --bmc1_ucm_init_mode                    2
% 19.47/3.00  --bmc1_ucm_cone_mode                    none
% 19.47/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.47/3.00  --bmc1_ucm_relax_model                  4
% 19.47/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.47/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.47/3.00  --bmc1_ucm_layered_model                none
% 19.47/3.00  --bmc1_ucm_max_lemma_size               10
% 19.47/3.00  
% 19.47/3.00  ------ AIG Options
% 19.47/3.00  
% 19.47/3.00  --aig_mode                              false
% 19.47/3.00  
% 19.47/3.00  ------ Instantiation Options
% 19.47/3.00  
% 19.47/3.00  --instantiation_flag                    true
% 19.47/3.00  --inst_sos_flag                         true
% 19.47/3.00  --inst_sos_phase                        true
% 19.47/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.47/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.47/3.00  --inst_lit_sel_side                     none
% 19.47/3.00  --inst_solver_per_active                1400
% 19.47/3.00  --inst_solver_calls_frac                1.
% 19.47/3.00  --inst_passive_queue_type               priority_queues
% 19.47/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.47/3.00  --inst_passive_queues_freq              [25;2]
% 19.47/3.00  --inst_dismatching                      true
% 19.47/3.00  --inst_eager_unprocessed_to_passive     true
% 19.47/3.00  --inst_prop_sim_given                   true
% 19.47/3.00  --inst_prop_sim_new                     false
% 19.47/3.00  --inst_subs_new                         false
% 19.47/3.00  --inst_eq_res_simp                      false
% 19.47/3.00  --inst_subs_given                       false
% 19.47/3.00  --inst_orphan_elimination               true
% 19.47/3.00  --inst_learning_loop_flag               true
% 19.47/3.00  --inst_learning_start                   3000
% 19.47/3.00  --inst_learning_factor                  2
% 19.47/3.00  --inst_start_prop_sim_after_learn       3
% 19.47/3.00  --inst_sel_renew                        solver
% 19.47/3.00  --inst_lit_activity_flag                true
% 19.47/3.00  --inst_restr_to_given                   false
% 19.47/3.00  --inst_activity_threshold               500
% 19.47/3.00  --inst_out_proof                        true
% 19.47/3.00  
% 19.47/3.00  ------ Resolution Options
% 19.47/3.00  
% 19.47/3.00  --resolution_flag                       false
% 19.47/3.00  --res_lit_sel                           adaptive
% 19.47/3.00  --res_lit_sel_side                      none
% 19.47/3.00  --res_ordering                          kbo
% 19.47/3.00  --res_to_prop_solver                    active
% 19.47/3.00  --res_prop_simpl_new                    false
% 19.47/3.00  --res_prop_simpl_given                  true
% 19.47/3.00  --res_passive_queue_type                priority_queues
% 19.47/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.47/3.00  --res_passive_queues_freq               [15;5]
% 19.47/3.00  --res_forward_subs                      full
% 19.47/3.00  --res_backward_subs                     full
% 19.47/3.00  --res_forward_subs_resolution           true
% 19.47/3.00  --res_backward_subs_resolution          true
% 19.47/3.00  --res_orphan_elimination                true
% 19.47/3.00  --res_time_limit                        2.
% 19.47/3.00  --res_out_proof                         true
% 19.47/3.00  
% 19.47/3.00  ------ Superposition Options
% 19.47/3.00  
% 19.47/3.00  --superposition_flag                    true
% 19.47/3.00  --sup_passive_queue_type                priority_queues
% 19.47/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.47/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.47/3.00  --demod_completeness_check              fast
% 19.47/3.00  --demod_use_ground                      true
% 19.47/3.00  --sup_to_prop_solver                    passive
% 19.47/3.00  --sup_prop_simpl_new                    true
% 19.47/3.00  --sup_prop_simpl_given                  true
% 19.47/3.00  --sup_fun_splitting                     true
% 19.47/3.00  --sup_smt_interval                      50000
% 19.47/3.00  
% 19.47/3.00  ------ Superposition Simplification Setup
% 19.47/3.00  
% 19.47/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.47/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.47/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.47/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.47/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.47/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.47/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.47/3.00  --sup_immed_triv                        [TrivRules]
% 19.47/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.47/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.47/3.00  --sup_immed_bw_main                     []
% 19.47/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.47/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.47/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.47/3.00  --sup_input_bw                          []
% 19.47/3.00  
% 19.47/3.00  ------ Combination Options
% 19.47/3.00  
% 19.47/3.00  --comb_res_mult                         3
% 19.47/3.00  --comb_sup_mult                         2
% 19.47/3.00  --comb_inst_mult                        10
% 19.47/3.00  
% 19.47/3.00  ------ Debug Options
% 19.47/3.00  
% 19.47/3.00  --dbg_backtrace                         false
% 19.47/3.00  --dbg_dump_prop_clauses                 false
% 19.47/3.00  --dbg_dump_prop_clauses_file            -
% 19.47/3.00  --dbg_out_stat                          false
% 19.47/3.00  
% 19.47/3.00  
% 19.47/3.00  
% 19.47/3.00  
% 19.47/3.00  ------ Proving...
% 19.47/3.00  
% 19.47/3.00  
% 19.47/3.00  % SZS status Theorem for theBenchmark.p
% 19.47/3.00  
% 19.47/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.47/3.00  
% 19.47/3.00  fof(f5,conjecture,(
% 19.47/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (k1_tsep_1(X0,X1,X2) = X0 => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2)))))))),
% 19.47/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.47/3.00  
% 19.47/3.00  fof(f6,negated_conjecture,(
% 19.47/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (k1_tsep_1(X0,X1,X2) = X0 => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2)))))))),
% 19.47/3.00    inference(negated_conjecture,[],[f5])).
% 19.47/3.00  
% 19.47/3.00  fof(f14,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : (((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) & k1_tsep_1(X0,X1,X2) = X0) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.47/3.00    inference(ennf_transformation,[],[f6])).
% 19.47/3.00  
% 19.47/3.00  fof(f15,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.47/3.00    inference(flattening,[],[f14])).
% 19.47/3.00  
% 19.47/3.00  fof(f18,plain,(
% 19.47/3.00    ! [X3,X0,X2,X1] : (sP1(X3,X0,X2,X1) <=> ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4)))),
% 19.47/3.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 19.47/3.00  
% 19.47/3.00  fof(f19,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (sP1(X3,X0,X2,X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.47/3.00    inference(definition_folding,[],[f15,f18])).
% 19.47/3.00  
% 19.47/3.00  fof(f33,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & ((! [X3] : (sP1(X3,X0,X2,X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | r3_tsep_1(X0,X1,X2))) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.47/3.00    inference(nnf_transformation,[],[f19])).
% 19.47/3.00  
% 19.47/3.00  fof(f34,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2)) & ((! [X3] : (sP1(X3,X0,X2,X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | r3_tsep_1(X0,X1,X2)) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.47/3.00    inference(flattening,[],[f33])).
% 19.47/3.00  
% 19.47/3.00  fof(f35,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2)) & ((! [X4] : (sP1(X4,X0,X2,X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | r3_tsep_1(X0,X1,X2)) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.47/3.00    inference(rectify,[],[f34])).
% 19.47/3.00  
% 19.47/3.00  fof(f39,plain,(
% 19.47/3.00    ( ! [X2,X0,X1] : (? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (~sP1(sK8,X0,X2,X1) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8))) )),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f38,plain,(
% 19.47/3.00    ( ! [X0,X1] : (? [X2] : ((? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2)) & ((! [X4] : (sP1(X4,X0,X2,X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | r3_tsep_1(X0,X1,X2)) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((? [X3] : (~sP1(X3,X0,sK7,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,sK7) | ~r3_tsep_1(X0,X1,sK7)) & ((! [X4] : (sP1(X4,X0,sK7,X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,sK7)) | r3_tsep_1(X0,X1,sK7)) & k1_tsep_1(X0,X1,sK7) = X0 & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f37,plain,(
% 19.47/3.00    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2)) & ((! [X4] : (sP1(X4,X0,X2,X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | r3_tsep_1(X0,X1,X2)) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (~sP1(X3,X0,X2,sK6) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(sK6,X2) | ~r3_tsep_1(X0,sK6,X2)) & ((! [X4] : (sP1(X4,X0,X2,sK6) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(sK6,X2)) | r3_tsep_1(X0,sK6,X2)) & k1_tsep_1(X0,sK6,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f36,plain,(
% 19.47/3.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~sP1(X3,X0,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2)) & ((! [X4] : (sP1(X4,X0,X2,X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | r3_tsep_1(X0,X1,X2)) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (~sP1(X3,sK5,X2,X1) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2) | ~r3_tsep_1(sK5,X1,X2)) & ((! [X4] : (sP1(X4,sK5,X2,X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | r3_tsep_1(sK5,X1,X2)) & k1_tsep_1(sK5,X1,X2) = sK5 & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f40,plain,(
% 19.47/3.00    ((((~sP1(sK8,sK5,sK7,sK6) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8)) | ~r1_tsep_1(sK6,sK7) | ~r3_tsep_1(sK5,sK6,sK7)) & ((! [X4] : (sP1(X4,sK5,sK7,sK6) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(sK6,sK7)) | r3_tsep_1(sK5,sK6,sK7)) & k1_tsep_1(sK5,sK6,sK7) = sK5 & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 19.47/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f35,f39,f38,f37,f36])).
% 19.47/3.00  
% 19.47/3.00  fof(f89,plain,(
% 19.47/3.00    k1_tsep_1(sK5,sK6,sK7) = sK5),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f16,plain,(
% 19.47/3.00    ! [X3,X2,X1,X0] : (sP0(X3,X2,X1,X0) <=> ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)))),
% 19.47/3.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 19.47/3.00  
% 19.47/3.00  fof(f20,plain,(
% 19.47/3.00    ! [X3,X2,X1,X0] : ((sP0(X3,X2,X1,X0) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~sP0(X3,X2,X1,X0)))),
% 19.47/3.00    inference(nnf_transformation,[],[f16])).
% 19.47/3.00  
% 19.47/3.00  fof(f21,plain,(
% 19.47/3.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 19.47/3.00    inference(rectify,[],[f20])).
% 19.47/3.00  
% 19.47/3.00  fof(f22,plain,(
% 19.47/3.00    ! [X3,X2,X1,X0] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4)) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) => ((~m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK2(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3))) & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(sK2(X0,X1,X2,X3))))),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f23,plain,(
% 19.47/3.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK2(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3))) & m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0) & v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3))) & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(sK2(X0,X1,X2,X3)))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 19.47/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 19.47/3.00  
% 19.47/3.00  fof(f49,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f88,plain,(
% 19.47/3.00    m1_pre_topc(sK7,sK5)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f47,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(sK2(X0,X1,X2,X3))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f2,axiom,(
% 19.47/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 19.47/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.47/3.00  
% 19.47/3.00  fof(f9,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.47/3.00    inference(ennf_transformation,[],[f2])).
% 19.47/3.00  
% 19.47/3.00  fof(f10,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(flattening,[],[f9])).
% 19.47/3.00  
% 19.47/3.00  fof(f42,plain,(
% 19.47/3.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f10])).
% 19.47/3.00  
% 19.47/3.00  fof(f48,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f82,plain,(
% 19.47/3.00    ~v2_struct_0(sK5)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f83,plain,(
% 19.47/3.00    v2_pre_topc(sK5)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f84,plain,(
% 19.47/3.00    l1_pre_topc(sK5)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f3,axiom,(
% 19.47/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2))))))),
% 19.47/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.47/3.00  
% 19.47/3.00  fof(f11,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.47/3.00    inference(ennf_transformation,[],[f3])).
% 19.47/3.00  
% 19.47/3.00  fof(f12,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(flattening,[],[f11])).
% 19.47/3.00  
% 19.47/3.00  fof(f17,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(definition_folding,[],[f12,f16])).
% 19.47/3.00  
% 19.47/3.00  fof(f24,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | (? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(nnf_transformation,[],[f17])).
% 19.47/3.00  
% 19.47/3.00  fof(f25,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | ? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (sP0(X3,X2,X1,X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(flattening,[],[f24])).
% 19.47/3.00  
% 19.47/3.00  fof(f26,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | ? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X4] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(rectify,[],[f25])).
% 19.47/3.00  
% 19.47/3.00  fof(f27,plain,(
% 19.47/3.00    ! [X2,X1,X0] : (? [X3] : (~sP0(X3,X2,X1,X0) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (~sP0(sK3(X0,X1,X2),X2,X1,X0) & l1_pre_topc(sK3(X0,X1,X2)) & v2_pre_topc(sK3(X0,X1,X2)) & ~v2_struct_0(sK3(X0,X1,X2))))),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f28,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (((r3_tsep_1(X0,X1,X2) | (~sP0(sK3(X0,X1,X2),X2,X1,X0) & l1_pre_topc(sK3(X0,X1,X2)) & v2_pre_topc(sK3(X0,X1,X2)) & ~v2_struct_0(sK3(X0,X1,X2))) | ~r1_tsep_1(X1,X2)) & ((! [X4] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 19.47/3.00  
% 19.47/3.00  fof(f64,plain,(
% 19.47/3.00    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | ~sP0(sK3(X0,X1,X2),X2,X1,X0) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f28])).
% 19.47/3.00  
% 19.47/3.00  fof(f85,plain,(
% 19.47/3.00    ~v2_struct_0(sK6)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f86,plain,(
% 19.47/3.00    m1_pre_topc(sK6,sK5)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f87,plain,(
% 19.47/3.00    ~v2_struct_0(sK7)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f59,plain,(
% 19.47/3.00    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f28])).
% 19.47/3.00  
% 19.47/3.00  fof(f90,plain,(
% 19.47/3.00    r1_tsep_1(sK6,sK7) | r3_tsep_1(sK5,sK6,sK7)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f61,plain,(
% 19.47/3.00    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | ~v2_struct_0(sK3(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f28])).
% 19.47/3.00  
% 19.47/3.00  fof(f62,plain,(
% 19.47/3.00    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | v2_pre_topc(sK3(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f28])).
% 19.47/3.00  
% 19.47/3.00  fof(f63,plain,(
% 19.47/3.00    ( ! [X2,X0,X1] : (r3_tsep_1(X0,X1,X2) | l1_pre_topc(sK3(X0,X1,X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f28])).
% 19.47/3.00  
% 19.47/3.00  fof(f4,axiom,(
% 19.47/3.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 19.47/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.47/3.00  
% 19.47/3.00  fof(f13,plain,(
% 19.47/3.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 19.47/3.00    inference(ennf_transformation,[],[f4])).
% 19.47/3.00  
% 19.47/3.00  fof(f65,plain,(
% 19.47/3.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f13])).
% 19.47/3.00  
% 19.47/3.00  fof(f29,plain,(
% 19.47/3.00    ! [X3,X0,X2,X1] : ((sP1(X3,X0,X2,X1) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X0,X3) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~sP1(X3,X0,X2,X1)))),
% 19.47/3.00    inference(nnf_transformation,[],[f18])).
% 19.47/3.00  
% 19.47/3.00  fof(f30,plain,(
% 19.47/3.00    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X4,X1,X0) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0) & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,X4,X2)) & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0) & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X5,X1,X0) & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0) | ~v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X1,X0,X5,X2)) | ~m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0) | ~v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X1,X0,X5,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP1(X0,X1,X2,X3)))),
% 19.47/3.00    inference(rectify,[],[f29])).
% 19.47/3.00  
% 19.47/3.00  fof(f31,plain,(
% 19.47/3.00    ! [X3,X2,X1,X0] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(X4,X1,X0) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X4)) & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0) & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,X4,X2)) & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0) & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ((~m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0) | ~v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(sK4(X0,X1,X2,X3))) & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0) & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2)) & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0) & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4(X0,X1,X2,X3))))),
% 19.47/3.00    introduced(choice_axiom,[])).
% 19.47/3.00  
% 19.47/3.00  fof(f32,plain,(
% 19.47/3.00    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0) | ~v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(sK4(X0,X1,X2,X3))) & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0) & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2)) & m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0) & v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3)) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4(X0,X1,X2,X3)))) & (! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(X5,X1,X0) & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X5)) | ~m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0) | ~v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X1,X0,X5,X2)) | ~m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0) | ~v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X1,X0,X5,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X5)) | ~sP1(X0,X1,X2,X3)))),
% 19.47/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 19.47/3.00  
% 19.47/3.00  fof(f70,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v1_funct_1(sK4(X0,X1,X2,X3))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f71,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f72,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f1,axiom,(
% 19.47/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 19.47/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.47/3.00  
% 19.47/3.00  fof(f7,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.47/3.00    inference(ennf_transformation,[],[f1])).
% 19.47/3.00  
% 19.47/3.00  fof(f8,plain,(
% 19.47/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.47/3.00    inference(flattening,[],[f7])).
% 19.47/3.00  
% 19.47/3.00  fof(f41,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f8])).
% 19.47/3.00  
% 19.47/3.00  fof(f95,plain,(
% 19.47/3.00    ~sP1(sK8,sK5,sK7,sK6) | ~r1_tsep_1(sK6,sK7) | ~r3_tsep_1(sK5,sK6,sK7)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f92,plain,(
% 19.47/3.00    ~v2_struct_0(sK8) | ~r1_tsep_1(sK6,sK7) | ~r3_tsep_1(sK5,sK6,sK7)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f93,plain,(
% 19.47/3.00    v2_pre_topc(sK8) | ~r1_tsep_1(sK6,sK7) | ~r3_tsep_1(sK5,sK6,sK7)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f94,plain,(
% 19.47/3.00    l1_pre_topc(sK8) | ~r1_tsep_1(sK6,sK7) | ~r3_tsep_1(sK5,sK6,sK7)),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f57,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f68,plain,(
% 19.47/3.00    ( ! [X2,X0,X5,X3,X1] : (v5_pre_topc(X5,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0) | ~v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X1,X0,X5,X2)) | ~m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0) | ~v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X1,X0,X5,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X5) | ~sP1(X0,X1,X2,X3)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f91,plain,(
% 19.47/3.00    ( ! [X4] : (sP1(X4,sK5,sK7,sK6) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | r3_tsep_1(sK5,sK6,sK7)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f40])).
% 19.47/3.00  
% 19.47/3.00  fof(f54,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f56,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f55,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f45,plain,(
% 19.47/3.00    ( ! [X2,X0,X5,X3,X1] : (v5_pre_topc(X5,k1_tsep_1(X3,X2,X1),X0) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),X1,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X5)) | ~m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),X2,X0) | ~v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5),u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X5) | ~sP0(X0,X1,X2,X3)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f50,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f52,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f51,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f53,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f58,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(sK2(X0,X1,X2,X3))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f23])).
% 19.47/3.00  
% 19.47/3.00  fof(f81,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | ~m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0) | ~v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(sK4(X0,X1,X2,X3))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f77,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f73,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f79,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f75,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f78,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f74,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f80,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f76,plain,(
% 19.47/3.00    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))) )),
% 19.47/3.00    inference(cnf_transformation,[],[f32])).
% 19.47/3.00  
% 19.47/3.00  fof(f60,plain,(
% 19.47/3.00    ( ! [X4,X2,X0,X1] : (sP0(X4,X2,X1,X0) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.47/3.00    inference(cnf_transformation,[],[f28])).
% 19.47/3.00  
% 19.47/3.00  cnf(c_47,negated_conjecture,
% 19.47/3.00      ( k1_tsep_1(sK5,sK6,sK7) = sK5 ),
% 19.47/3.00      inference(cnf_transformation,[],[f89]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8387,negated_conjecture,
% 19.47/3.00      ( k1_tsep_1(sK5,sK6,sK7) = sK5 ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_47]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11,plain,
% 19.47/3.00      ( sP0(X0,X1,X2,X3)
% 19.47/3.00      | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) ),
% 19.47/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8411,plain,
% 19.47/3.00      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.00      | m1_subset_1(sK2(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)))) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_11]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9331,plain,
% 19.47/3.00      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | m1_subset_1(sK2(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8411]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_10985,plain,
% 19.47/3.00      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | m1_subset_1(sK2(X0_54,sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_8387,c_9331]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_48,negated_conjecture,
% 19.47/3.00      ( m1_pre_topc(sK7,sK5) ),
% 19.47/3.00      inference(cnf_transformation,[],[f88]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8386,negated_conjecture,
% 19.47/3.00      ( m1_pre_topc(sK7,sK5) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_48]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9355,plain,
% 19.47/3.00      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8386]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_13,plain,
% 19.47/3.00      ( sP0(X0,X1,X2,X3) | v1_funct_1(sK2(X0,X1,X2,X3)) ),
% 19.47/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8409,plain,
% 19.47/3.00      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.00      | v1_funct_1(sK2(X0_54,X1_54,X2_54,X3_54)) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_13]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9333,plain,
% 19.47/3.00      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | v1_funct_1(sK2(X0_54,X1_54,X2_54,X3_54)) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8409]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_1,plain,
% 19.47/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.47/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.47/3.00      | ~ m1_pre_topc(X3,X4)
% 19.47/3.00      | ~ m1_pre_topc(X3,X1)
% 19.47/3.00      | ~ m1_pre_topc(X1,X4)
% 19.47/3.00      | v2_struct_0(X4)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_pre_topc(X2)
% 19.47/3.00      | ~ v2_pre_topc(X4)
% 19.47/3.00      | ~ l1_pre_topc(X2)
% 19.47/3.00      | ~ l1_pre_topc(X4)
% 19.47/3.00      | ~ v1_funct_1(X0)
% 19.47/3.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 19.47/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8420,plain,
% 19.47/3.00      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 19.47/3.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X0_54)
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X3_54)
% 19.47/3.00      | ~ m1_pre_topc(X0_54,X3_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(X3_54)
% 19.47/3.00      | ~ v2_pre_topc(X3_54)
% 19.47/3.00      | ~ v2_pre_topc(X1_54)
% 19.47/3.00      | ~ l1_pre_topc(X3_54)
% 19.47/3.00      | ~ l1_pre_topc(X1_54)
% 19.47/3.00      | ~ v1_funct_1(X0_55)
% 19.47/3.00      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_1]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9322,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_55)
% 19.47/3.00      | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 19.47/3.00      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 19.47/3.00      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X3_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X3_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X3_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | v1_funct_1(X0_55) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8420]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11065,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | v1_funct_2(sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,X2_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X2_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_10985,c_9322]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_12,plain,
% 19.47/3.00      ( sP0(X0,X1,X2,X3)
% 19.47/3.00      | v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) ),
% 19.47/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8410,plain,
% 19.47/3.00      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.00      | v1_funct_2(sK2(X0_54,X1_54,X2_54,X3_54),u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_12]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9332,plain,
% 19.47/3.00      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | v1_funct_2(sK2(X0_54,X1_54,X2_54,X3_54),u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8410]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_10527,plain,
% 19.47/3.00      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | v1_funct_2(sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_8387,c_9332]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11292,plain,
% 19.47/3.00      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,X2_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X2_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.00      inference(global_propositional_subsumption,
% 19.47/3.00                [status(thm)],
% 19.47/3.00                [c_11065,c_10527]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11293,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,X2_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X2_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.00      inference(renaming,[status(thm)],[c_11292]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11298,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK5,X1_54,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,X2_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X2_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X2_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X2_54) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_9333,c_11293]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11418,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(X1_54,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | m1_pre_topc(sK7,X1_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,X1_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_9355,c_11298]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11494,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(sK5) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_9355,c_11418]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_54,negated_conjecture,
% 19.47/3.00      ( ~ v2_struct_0(sK5) ),
% 19.47/3.00      inference(cnf_transformation,[],[f82]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_55,plain,
% 19.47/3.00      ( v2_struct_0(sK5) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_53,negated_conjecture,
% 19.47/3.00      ( v2_pre_topc(sK5) ),
% 19.47/3.00      inference(cnf_transformation,[],[f83]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_56,plain,
% 19.47/3.00      ( v2_pre_topc(sK5) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_52,negated_conjecture,
% 19.47/3.00      ( l1_pre_topc(sK5) ),
% 19.47/3.00      inference(cnf_transformation,[],[f84]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_57,plain,
% 19.47/3.00      ( l1_pre_topc(sK5) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11503,plain,
% 19.47/3.00      ( l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top ),
% 19.47/3.00      inference(global_propositional_subsumption,
% 19.47/3.00                [status(thm)],
% 19.47/3.00                [c_11494,c_55,c_56,c_57]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_11504,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.00      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.00      inference(renaming,[status(thm)],[c_11503]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_18,plain,
% 19.47/3.00      ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
% 19.47/3.00      | r3_tsep_1(X0,X1,X2)
% 19.47/3.00      | ~ r1_tsep_1(X1,X2)
% 19.47/3.00      | ~ m1_pre_topc(X2,X0)
% 19.47/3.00      | ~ m1_pre_topc(X1,X0)
% 19.47/3.00      | v2_struct_0(X0)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_pre_topc(X0)
% 19.47/3.00      | ~ l1_pre_topc(X0) ),
% 19.47/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8407,plain,
% 19.47/3.00      ( ~ sP0(sK3(X0_54,X1_54,X2_54),X2_54,X1_54,X0_54)
% 19.47/3.00      | r3_tsep_1(X0_54,X1_54,X2_54)
% 19.47/3.00      | ~ r1_tsep_1(X1_54,X2_54)
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X0_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,X0_54)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(X2_54)
% 19.47/3.00      | ~ v2_pre_topc(X0_54)
% 19.47/3.00      | ~ l1_pre_topc(X0_54) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_18]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9335,plain,
% 19.47/3.00      ( sP0(sK3(X0_54,X1_54,X2_54),X2_54,X1_54,X0_54) != iProver_top
% 19.47/3.00      | r3_tsep_1(X0_54,X1_54,X2_54) = iProver_top
% 19.47/3.00      | r1_tsep_1(X1_54,X2_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 19.47/3.00      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X2_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8407]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_12743,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.00      | r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.00      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.00      | v2_struct_0(sK6) = iProver_top
% 19.47/3.00      | v2_struct_0(sK7) = iProver_top
% 19.47/3.00      | v2_struct_0(sK5) = iProver_top
% 19.47/3.00      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.00      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_11504,c_9335]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_51,negated_conjecture,
% 19.47/3.00      ( ~ v2_struct_0(sK6) ),
% 19.47/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_58,plain,
% 19.47/3.00      ( v2_struct_0(sK6) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_50,negated_conjecture,
% 19.47/3.00      ( m1_pre_topc(sK6,sK5) ),
% 19.47/3.00      inference(cnf_transformation,[],[f86]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_59,plain,
% 19.47/3.00      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_49,negated_conjecture,
% 19.47/3.00      ( ~ v2_struct_0(sK7) ),
% 19.47/3.00      inference(cnf_transformation,[],[f87]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_60,plain,
% 19.47/3.00      ( v2_struct_0(sK7) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_61,plain,
% 19.47/3.00      ( m1_pre_topc(sK7,sK5) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_23,plain,
% 19.47/3.00      ( ~ r3_tsep_1(X0,X1,X2)
% 19.47/3.00      | r1_tsep_1(X1,X2)
% 19.47/3.00      | ~ m1_pre_topc(X2,X0)
% 19.47/3.00      | ~ m1_pre_topc(X1,X0)
% 19.47/3.00      | v2_struct_0(X0)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_pre_topc(X0)
% 19.47/3.00      | ~ l1_pre_topc(X0) ),
% 19.47/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_46,negated_conjecture,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7) | r1_tsep_1(sK6,sK7) ),
% 19.47/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_3558,plain,
% 19.47/3.00      ( r1_tsep_1(X0,X1)
% 19.47/3.00      | r1_tsep_1(sK6,sK7)
% 19.47/3.00      | ~ m1_pre_topc(X1,X2)
% 19.47/3.00      | ~ m1_pre_topc(X0,X2)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | v2_struct_0(X0)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | ~ v2_pre_topc(X2)
% 19.47/3.00      | ~ l1_pre_topc(X2)
% 19.47/3.00      | sK6 != X0
% 19.47/3.00      | sK7 != X1
% 19.47/3.00      | sK5 != X2 ),
% 19.47/3.00      inference(resolution_lifted,[status(thm)],[c_23,c_46]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_3559,plain,
% 19.47/3.00      ( r1_tsep_1(sK6,sK7)
% 19.47/3.00      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.00      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.00      | v2_struct_0(sK6)
% 19.47/3.00      | v2_struct_0(sK7)
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(unflattening,[status(thm)],[c_3558]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_3560,plain,
% 19.47/3.00      ( r1_tsep_1(sK6,sK7) = iProver_top
% 19.47/3.00      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(sK6) = iProver_top
% 19.47/3.00      | v2_struct_0(sK7) = iProver_top
% 19.47/3.00      | v2_struct_0(sK5) = iProver_top
% 19.47/3.00      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_3559]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_21,plain,
% 19.47/3.00      ( r3_tsep_1(X0,X1,X2)
% 19.47/3.00      | ~ r1_tsep_1(X1,X2)
% 19.47/3.00      | ~ m1_pre_topc(X2,X0)
% 19.47/3.00      | ~ m1_pre_topc(X1,X0)
% 19.47/3.00      | v2_struct_0(X0)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_struct_0(sK3(X0,X1,X2))
% 19.47/3.00      | ~ v2_pre_topc(X0)
% 19.47/3.00      | ~ l1_pre_topc(X0) ),
% 19.47/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8404,plain,
% 19.47/3.00      ( r3_tsep_1(X0_54,X1_54,X2_54)
% 19.47/3.00      | ~ r1_tsep_1(X1_54,X2_54)
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X0_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,X0_54)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(X2_54)
% 19.47/3.00      | ~ v2_struct_0(sK3(X0_54,X1_54,X2_54))
% 19.47/3.00      | ~ v2_pre_topc(X0_54)
% 19.47/3.00      | ~ l1_pre_topc(X0_54) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_21]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9432,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,X0_54,X1_54)
% 19.47/3.00      | ~ r1_tsep_1(X0_54,X1_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,sK5)
% 19.47/3.00      | ~ m1_pre_topc(X0_54,sK5)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | ~ v2_struct_0(sK3(sK5,X0_54,X1_54))
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_8404]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9619,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.00      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.00      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.00      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.00      | ~ v2_struct_0(sK3(sK5,sK6,sK7))
% 19.47/3.00      | v2_struct_0(sK6)
% 19.47/3.00      | v2_struct_0(sK7)
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_9432]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9620,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.00      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.00      | v2_struct_0(sK6) = iProver_top
% 19.47/3.00      | v2_struct_0(sK7) = iProver_top
% 19.47/3.00      | v2_struct_0(sK5) = iProver_top
% 19.47/3.00      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_9619]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_20,plain,
% 19.47/3.00      ( r3_tsep_1(X0,X1,X2)
% 19.47/3.00      | ~ r1_tsep_1(X1,X2)
% 19.47/3.00      | ~ m1_pre_topc(X2,X0)
% 19.47/3.00      | ~ m1_pre_topc(X1,X0)
% 19.47/3.00      | v2_struct_0(X0)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_pre_topc(X0)
% 19.47/3.00      | v2_pre_topc(sK3(X0,X1,X2))
% 19.47/3.00      | ~ l1_pre_topc(X0) ),
% 19.47/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8405,plain,
% 19.47/3.00      ( r3_tsep_1(X0_54,X1_54,X2_54)
% 19.47/3.00      | ~ r1_tsep_1(X1_54,X2_54)
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X0_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,X0_54)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(X2_54)
% 19.47/3.00      | ~ v2_pre_topc(X0_54)
% 19.47/3.00      | v2_pre_topc(sK3(X0_54,X1_54,X2_54))
% 19.47/3.00      | ~ l1_pre_topc(X0_54) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_20]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9433,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,X0_54,X1_54)
% 19.47/3.00      | ~ r1_tsep_1(X0_54,X1_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,sK5)
% 19.47/3.00      | ~ m1_pre_topc(X0_54,sK5)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | v2_pre_topc(sK3(sK5,X0_54,X1_54))
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_8405]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9624,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.00      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.00      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.00      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.00      | v2_struct_0(sK6)
% 19.47/3.00      | v2_struct_0(sK7)
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | v2_pre_topc(sK3(sK5,sK6,sK7))
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_9433]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9625,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.00      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(sK6) = iProver_top
% 19.47/3.00      | v2_struct_0(sK7) = iProver_top
% 19.47/3.00      | v2_struct_0(sK5) = iProver_top
% 19.47/3.00      | v2_pre_topc(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.00      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_9624]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_19,plain,
% 19.47/3.00      ( r3_tsep_1(X0,X1,X2)
% 19.47/3.00      | ~ r1_tsep_1(X1,X2)
% 19.47/3.00      | ~ m1_pre_topc(X2,X0)
% 19.47/3.00      | ~ m1_pre_topc(X1,X0)
% 19.47/3.00      | v2_struct_0(X0)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_pre_topc(X0)
% 19.47/3.00      | ~ l1_pre_topc(X0)
% 19.47/3.00      | l1_pre_topc(sK3(X0,X1,X2)) ),
% 19.47/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8406,plain,
% 19.47/3.00      ( r3_tsep_1(X0_54,X1_54,X2_54)
% 19.47/3.00      | ~ r1_tsep_1(X1_54,X2_54)
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X0_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,X0_54)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(X2_54)
% 19.47/3.00      | ~ v2_pre_topc(X0_54)
% 19.47/3.00      | ~ l1_pre_topc(X0_54)
% 19.47/3.00      | l1_pre_topc(sK3(X0_54,X1_54,X2_54)) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_19]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9434,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,X0_54,X1_54)
% 19.47/3.00      | ~ r1_tsep_1(X0_54,X1_54)
% 19.47/3.00      | ~ m1_pre_topc(X1_54,sK5)
% 19.47/3.00      | ~ m1_pre_topc(X0_54,sK5)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | l1_pre_topc(sK3(sK5,X0_54,X1_54))
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_8406]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9714,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.00      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.00      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.00      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.00      | v2_struct_0(sK6)
% 19.47/3.00      | v2_struct_0(sK7)
% 19.47/3.00      | v2_struct_0(sK5)
% 19.47/3.00      | ~ v2_pre_topc(sK5)
% 19.47/3.00      | l1_pre_topc(sK3(sK5,sK6,sK7))
% 19.47/3.00      | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_9434]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9715,plain,
% 19.47/3.00      ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.00      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.00      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.00      | v2_struct_0(sK6) = iProver_top
% 19.47/3.00      | v2_struct_0(sK7) = iProver_top
% 19.47/3.00      | v2_struct_0(sK5) = iProver_top
% 19.47/3.00      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.00      | l1_pre_topc(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_9714]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_24,plain,
% 19.47/3.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 19.47/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8401,plain,
% 19.47/3.00      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_24]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_12165,plain,
% 19.47/3.00      ( m1_pre_topc(sK5,sK5) | ~ l1_pre_topc(sK5) ),
% 19.47/3.00      inference(instantiation,[status(thm)],[c_8401]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_12166,plain,
% 19.47/3.00      ( m1_pre_topc(sK5,sK5) = iProver_top
% 19.47/3.00      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_12165]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_13579,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.00      | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
% 19.47/3.00      inference(global_propositional_subsumption,
% 19.47/3.00                [status(thm)],
% 19.47/3.00                [c_12743,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.00                 c_9620,c_9625,c_9715,c_12166]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9341,plain,
% 19.47/3.00      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8401]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_36,plain,
% 19.47/3.00      ( sP1(X0,X1,X2,X3) | v1_funct_1(sK4(X0,X1,X2,X3)) ),
% 19.47/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8390,plain,
% 19.47/3.00      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.00      | v1_funct_1(sK4(X0_54,X1_54,X2_54,X3_54)) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_36]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9352,plain,
% 19.47/3.00      ( sP1(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | v1_funct_1(sK4(X0_54,X1_54,X2_54,X3_54)) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8390]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_35,plain,
% 19.47/3.00      ( sP1(X0,X1,X2,X3)
% 19.47/3.00      | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0)) ),
% 19.47/3.00      inference(cnf_transformation,[],[f71]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8391,plain,
% 19.47/3.00      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.00      | v1_funct_2(sK4(X0_54,X1_54,X2_54,X3_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_35]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9351,plain,
% 19.47/3.00      ( sP1(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | v1_funct_2(sK4(X0_54,X1_54,X2_54,X3_54),u1_struct_0(X1_54),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8391]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_34,plain,
% 19.47/3.00      ( sP1(X0,X1,X2,X3)
% 19.47/3.00      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 19.47/3.00      inference(cnf_transformation,[],[f72]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8392,plain,
% 19.47/3.00      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.00      | m1_subset_1(sK4(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_34]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9350,plain,
% 19.47/3.00      ( sP1(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | m1_subset_1(sK4(X0_54,X1_54,X2_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8392]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_0,plain,
% 19.47/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.47/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.47/3.00      | ~ m1_pre_topc(X3,X1)
% 19.47/3.00      | v2_struct_0(X1)
% 19.47/3.00      | v2_struct_0(X2)
% 19.47/3.00      | ~ v2_pre_topc(X2)
% 19.47/3.00      | ~ v2_pre_topc(X1)
% 19.47/3.00      | ~ l1_pre_topc(X2)
% 19.47/3.00      | ~ l1_pre_topc(X1)
% 19.47/3.00      | ~ v1_funct_1(X0)
% 19.47/3.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 19.47/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_8421,plain,
% 19.47/3.00      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 19.47/3.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 19.47/3.00      | ~ m1_pre_topc(X2_54,X0_54)
% 19.47/3.00      | v2_struct_0(X0_54)
% 19.47/3.00      | v2_struct_0(X1_54)
% 19.47/3.00      | ~ v2_pre_topc(X0_54)
% 19.47/3.00      | ~ v2_pre_topc(X1_54)
% 19.47/3.00      | ~ l1_pre_topc(X0_54)
% 19.47/3.00      | ~ l1_pre_topc(X1_54)
% 19.47/3.00      | ~ v1_funct_1(X0_55)
% 19.47/3.00      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54) ),
% 19.47/3.00      inference(subtyping,[status(esa)],[c_0]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_9321,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_55,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_55,X2_54)
% 19.47/3.00      | v1_funct_2(X0_55,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 19.47/3.00      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 19.47/3.00      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | v1_funct_1(X0_55) != iProver_top ),
% 19.47/3.00      inference(predicate_to_equality,[status(thm)],[c_8421]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_10519,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X4_54)
% 19.47/3.00      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | v1_funct_2(sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 19.47/3.00      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_9350,c_9321]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_13378,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X4_54)
% 19.47/3.00      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.00      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.00      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.00      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.00      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.00      | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
% 19.47/3.00      inference(superposition,[status(thm)],[c_9351,c_10519]) ).
% 19.47/3.00  
% 19.47/3.00  cnf(c_13672,plain,
% 19.47/3.00      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X4_54)
% 19.47/3.00      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.00      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9352,c_13378]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13778,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k2_tmap_1(X0_54,X1_54,sK4(X1_54,X0_54,X2_54,X3_54),X0_54)
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9341,c_13672]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3561,plain,
% 19.47/3.01      ( r1_tsep_1(sK6,sK7) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3559,c_54,c_53,c_52,c_51,c_50,c_49,c_48]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_41,negated_conjecture,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.01      inference(cnf_transformation,[],[f95]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3659,plain,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6) | ~ r3_tsep_1(sK5,sK6,sK7) ),
% 19.47/3.01      inference(backward_subsumption_resolution,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3561,c_41]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8376,plain,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6) | ~ r3_tsep_1(sK5,sK6,sK7) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_3659]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9365,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8376]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14347,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13778,c_9365]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_44,negated_conjecture,
% 19.47/3.01      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ v2_struct_0(sK8) ),
% 19.47/3.01      inference(cnf_transformation,[],[f92]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_66,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | v2_struct_0(sK8) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_43,negated_conjecture,
% 19.47/3.01      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | v2_pre_topc(sK8) ),
% 19.47/3.01      inference(cnf_transformation,[],[f93]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_67,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_42,negated_conjecture,
% 19.47/3.01      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | l1_pre_topc(sK8) ),
% 19.47/3.01      inference(cnf_transformation,[],[f94]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_68,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14496,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_14347,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14502,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13579,c_14496]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11066,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10985,c_9321]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11074,plain,
% 19.47/3.01      ( l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_11066,c_55,c_56,c_57,c_10527]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11075,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(X0_54,sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_11074]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11080,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(X1_54)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),X1_54)
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_pre_topc(X1_54,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9333,c_11075]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11346,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),sK7)
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9355,c_11080]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12745,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v2_struct_0(sK6) = iProver_top
% 19.47/3.01      | v2_struct_0(sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_11346,c_9335]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13113,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_12745,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9620,c_9625,c_9715]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13114,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_13113]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14504,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13114,c_14496]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16362,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_14502,c_14504]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
% 19.47/3.01      inference(cnf_transformation,[],[f57]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8419,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_3]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9323,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8419]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10571,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9323]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27808,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16362,c_10571]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9431,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,X0_54,X1_54),X1_54,X0_54,sK5)
% 19.47/3.01      | r3_tsep_1(sK5,X0_54,X1_54)
% 19.47/3.01      | ~ r1_tsep_1(X0_54,X1_54)
% 19.47/3.01      | ~ m1_pre_topc(X1_54,sK5)
% 19.47/3.01      | ~ m1_pre_topc(X0_54,sK5)
% 19.47/3.01      | v2_struct_0(X0_54)
% 19.47/3.01      | v2_struct_0(X1_54)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | ~ l1_pre_topc(sK5) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8407]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9719,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.01      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.01      | v2_struct_0(sK6)
% 19.47/3.01      | v2_struct_0(sK7)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | ~ l1_pre_topc(sK5) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_9431]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9720,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK6) = iProver_top
% 19.47/3.01      | v2_struct_0(sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9719]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27906,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_27808,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_9720,c_14347]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38,plain,
% 19.47/3.01      ( ~ sP1(X0,X1,X2,X3)
% 19.47/3.01      | v5_pre_topc(X4,X1,X0)
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
% 19.47/3.01      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
% 19.47/3.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 19.47/3.01      | ~ v1_funct_1(X4)
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(X1,X0,X4,X3)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f68]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8389,plain,
% 19.47/3.01      ( ~ sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v5_pre_topc(X0_55,X1_54,X0_54)
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),X2_54,X0_54)
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),X3_54,X0_54)
% 19.47/3.01      | ~ v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(X0_54))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X0_54))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54))
% 19.47/3.01      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54))))
% 19.47/3.01      | ~ v1_funct_1(X0_55)
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_38]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9353,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(X0_55,X1_54,X0_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),X2_54,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),X3_54,X0_54) != iProver_top
% 19.47/3.01      | v1_funct_2(X0_55,u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | v1_funct_1(X0_55) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X2_54)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(X1_54,X0_54,X0_55,X3_54)) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8389]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27910,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP1(sK3(sK5,sK6,sK7),sK5,sK7,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_27906,c_9353]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_45,negated_conjecture,
% 19.47/3.01      ( sP1(X0,sK5,sK7,sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | v2_struct_0(X0)
% 19.47/3.01      | ~ v2_pre_topc(X0)
% 19.47/3.01      | ~ l1_pre_topc(X0) ),
% 19.47/3.01      inference(cnf_transformation,[],[f91]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8388,negated_conjecture,
% 19.47/3.01      ( sP1(X0_54,sK5,sK7,sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | v2_struct_0(X0_54)
% 19.47/3.01      | ~ v2_pre_topc(X0_54)
% 19.47/3.01      | ~ l1_pre_topc(X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_45]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10083,plain,
% 19.47/3.01      ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v2_pre_topc(sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ l1_pre_topc(sK3(sK5,sK6,sK7)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8388]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10084,plain,
% 19.47/3.01      ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_10083]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10154,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8409]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10155,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_10154]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_6,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3))) ),
% 19.47/3.01      inference(cnf_transformation,[],[f54]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8416,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54))) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_6]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9326,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8416]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10705,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9326]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27809,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16362,c_10705]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27816,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_27809,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_9720,c_14347]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_4,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),X1,X0) ),
% 19.47/3.01      inference(cnf_transformation,[],[f56]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8418,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),X1_54,X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_4]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9324,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),X1_54,X0_54) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8418]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11154,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5)),sK7,X0_54) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9324]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27807,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16362,c_11154]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27858,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_27807,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_9720,c_14347]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_5,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,sK2(X0,X1,X2,X3)),u1_struct_0(X1),u1_struct_0(X0)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f55]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8417,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_5]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9325,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8417]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11519,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK7,sK2(X0_54,sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9325]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27806,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16362,c_11519]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27863,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_27806,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_9720,c_14347]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27914,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_27910]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15,plain,
% 19.47/3.01      ( ~ sP0(X0,X1,X2,X3)
% 19.47/3.01      | v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0)
% 19.47/3.01      | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),X1,X0)
% 19.47/3.01      | ~ v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),X2,X0)
% 19.47/3.01      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 19.47/3.01      | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),u1_struct_0(X1),u1_struct_0(X0))
% 19.47/3.01      | ~ v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),u1_struct_0(X2),u1_struct_0(X0))
% 19.47/3.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 19.47/3.01      | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 19.47/3.01      | ~ m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
% 19.47/3.01      | ~ v1_funct_1(X4)
% 19.47/3.01      | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X1,X4))
% 19.47/3.01      | ~ v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,X4)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f45]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8408,plain,
% 19.47/3.01      ( ~ sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v5_pre_topc(X0_55,k1_tsep_1(X3_54,X2_54,X1_54),X0_54)
% 19.47/3.01      | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),X1_54,X0_54)
% 19.47/3.01      | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),X2_54,X0_54)
% 19.47/3.01      | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54))
% 19.47/3.01      | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 19.47/3.01      | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),u1_struct_0(X2_54),u1_struct_0(X0_54))
% 19.47/3.01      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54))))
% 19.47/3.01      | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 19.47/3.01      | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
% 19.47/3.01      | ~ v1_funct_1(X0_55)
% 19.47/3.01      | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55))
% 19.47/3.01      | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_15]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9334,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(X0_55,k1_tsep_1(X3_54,X2_54,X1_54),X0_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),X1_54,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),X2_54,X0_54) != iProver_top
% 19.47/3.01      | v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X1_54)),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | v1_funct_1(X0_55) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_55)) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_55)) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8408]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10488,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(X0_55,k1_tsep_1(sK5,sK6,sK7),X0_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55),sK6,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK7,X0_55),sK7,X0_54) != iProver_top
% 19.47/3.01      | v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK7,X0_55),u1_struct_0(sK7),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | v1_funct_1(X0_55) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK6,X0_55)) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,X0_54,k1_tsep_1(sK5,sK6,sK7),sK7,X0_55)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9334]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10489,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(X0_55,sK5,X0_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55),sK6,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),sK7,X0_54) != iProver_top
% 19.47/3.01      | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55),u1_struct_0(sK6),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),u1_struct_0(sK7),u1_struct_0(X0_54)) != iProver_top
% 19.47/3.01      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0_54)))) != iProver_top
% 19.47/3.01      | v1_funct_1(X0_55) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK6,X0_55)) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK7,X0_55)) != iProver_top ),
% 19.47/3.01      inference(light_normalisation,[status(thm)],[c_10488,c_8387]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27805,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16362,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27923,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_27805,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_9720,c_14347]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8384,negated_conjecture,
% 19.47/3.01      ( m1_pre_topc(sK6,sK5) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_50]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9357,plain,
% 19.47/3.01      ( m1_pre_topc(sK6,sK5) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8384]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11419,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(X1_54,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,X1_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,X1_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9357,c_11298]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11510,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9357,c_11419]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11778,plain,
% 19.47/3.01      ( l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_11510,c_55,c_56,c_57]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11779,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_11778]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12742,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v2_struct_0(sK6) = iProver_top
% 19.47/3.01      | v2_struct_0(sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_11779,c_9335]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13445,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_12742,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9620,c_9625,c_9715,c_12166]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14503,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13445,c_14496]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11347,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK2(X0_54,sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK2(X0_54,sK7,sK6,sK5),sK6)
% 19.47/3.01      | sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9357,c_11080]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12744,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v2_struct_0(sK6) = iProver_top
% 19.47/3.01      | v2_struct_0(sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_11347,c_9335]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12873,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_12744,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9620,c_9625,c_9715]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12874,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) = iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_12873]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14505,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_12874,c_14496]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16512,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_14503,c_14505]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3))) ),
% 19.47/3.01      inference(cnf_transformation,[],[f50]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8412,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54))) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_10]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9330,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8412]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10759,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9330]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28183,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16512,c_10759]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28258,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_28183,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),X2,X0) ),
% 19.47/3.01      inference(cnf_transformation,[],[f52]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8414,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),X2_54,X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_8]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9328,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),X2_54,X0_54) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8414]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11226,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5)),sK6,X0_54) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9328]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28182,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16512,c_11226]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28263,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_28182,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),u1_struct_0(X2),u1_struct_0(X0)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f51]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8413,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X2_54),u1_struct_0(X0_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_9]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9329,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),u1_struct_0(X2_54),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8413]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_11651,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(X0_54)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9329]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28181,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16512,c_11651]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28354,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_28181,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_7,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3,X0,k1_tsep_1(X3,X2,X1),X2,sK2(X0,X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
% 19.47/3.01      inference(cnf_transformation,[],[f53]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8415,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_7]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9327,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,sK2(X0_54,X1_54,X2_54,X3_54)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8415]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12295,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,X0_54,sK5,sK6,sK2(X0_54,sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0_54)))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9327]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28180,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16512,c_12295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28359,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_28180,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32688,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_27910,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_9620,c_9625,c_9715,c_10084,c_10155,
% 19.47/3.01                 c_14347,c_27816,c_27858,c_27863,c_27914,c_27923,c_28180,
% 19.47/3.01                 c_28181,c_28182,c_28183]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32692,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10985,c_32688]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32841,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_32692,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32845,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10527,c_32841]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32848,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_32845,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_2,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
% 19.47/3.01      | ~ v1_funct_2(sK2(X0,X1,X2,X3),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
% 19.47/3.01      | ~ m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
% 19.47/3.01      | ~ v1_funct_1(sK2(X0,X1,X2,X3)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_325,plain,
% 19.47/3.01      ( ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0)
% 19.47/3.01      | sP0(X0,X1,X2,X3) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_2,c_13,c_12,c_11]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_326,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | ~ v5_pre_topc(sK2(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1),X0) ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_325]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8378,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | ~ v5_pre_topc(sK2(X0_54,X1_54,X2_54,X3_54),k1_tsep_1(X3_54,X2_54,X1_54),X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_326]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9363,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(X0_54,X1_54,X2_54,X3_54),k1_tsep_1(X3_54,X2_54,X1_54),X0_54) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8378]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10295,plain,
% 19.47/3.01      ( sP0(X0_54,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(X0_54,sK7,sK6,sK5),sK5,X0_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_8387,c_9363]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32852,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_32848,c_10295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32919,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_32852,c_27923]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10518,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X5_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v1_funct_2(sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X5_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,X5_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X5_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X5_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X5_54) != iProver_top
% 19.47/3.01      | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9350,c_9322]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13274,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X5_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X5_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,X5_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X5_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X5_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X5_54) != iProver_top
% 19.47/3.01      | v1_funct_1(sK4(X1_54,X0_54,X2_54,X3_54)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9351,c_10518]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15381,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X5_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X5_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,X5_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X5_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X5_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X5_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9352,c_13274]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15397,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X4_54)) = k3_tmap_1(X4_54,X1_54,X0_54,X4_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,X4_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X4_54,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X4_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X4_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X4_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9341,c_15381]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15776,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k3_tmap_1(X0_54,X1_54,X0_54,X0_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9341,c_15397]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8500,plain,
% 19.47/3.01      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8401]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16002,plain,
% 19.47/3.01      ( sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k3_tmap_1(X0_54,X1_54,X0_54,X0_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_15776,c_8500]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16003,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(X0_54)) = k3_tmap_1(X0_54,X1_54,X0_54,X0_54,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_16002]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16008,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16003,c_9365]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16219,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_16008,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16227,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13579,c_16219]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32963,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_32919,c_16227]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16229,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5)) = k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13114,c_16219]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32965,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_32919,c_16229]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_33463,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_32963,c_32965]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_42280,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK5,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK5)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_33463,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3524,plain,
% 19.47/3.01      ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
% 19.47/3.01      | ~ r1_tsep_1(X1,X2)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(X2,X0)
% 19.47/3.01      | ~ m1_pre_topc(X1,X0)
% 19.47/3.01      | v2_struct_0(X0)
% 19.47/3.01      | v2_struct_0(X1)
% 19.47/3.01      | v2_struct_0(X2)
% 19.47/3.01      | ~ v2_pre_topc(X0)
% 19.47/3.01      | ~ l1_pre_topc(X0)
% 19.47/3.01      | l1_pre_topc(sK8)
% 19.47/3.01      | sK6 != X1
% 19.47/3.01      | sK7 != X2
% 19.47/3.01      | sK5 != X0 ),
% 19.47/3.01      inference(resolution_lifted,[status(thm)],[c_18,c_42]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3525,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.01      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.01      | v2_struct_0(sK6)
% 19.47/3.01      | v2_struct_0(sK7)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | ~ l1_pre_topc(sK5)
% 19.47/3.01      | l1_pre_topc(sK8) ),
% 19.47/3.01      inference(unflattening,[status(thm)],[c_3524]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3527,plain,
% 19.47/3.01      ( ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | l1_pre_topc(sK8) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3525,c_54,c_53,c_52,c_51,c_50,c_49,c_48]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3528,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | l1_pre_topc(sK8) ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_3527]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3587,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) | l1_pre_topc(sK8) ),
% 19.47/3.01      inference(backward_subsumption_resolution,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3561,c_3528]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3588,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_3587]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3507,plain,
% 19.47/3.01      ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
% 19.47/3.01      | ~ r1_tsep_1(X1,X2)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(X2,X0)
% 19.47/3.01      | ~ m1_pre_topc(X1,X0)
% 19.47/3.01      | v2_struct_0(X0)
% 19.47/3.01      | v2_struct_0(X1)
% 19.47/3.01      | v2_struct_0(X2)
% 19.47/3.01      | ~ v2_pre_topc(X0)
% 19.47/3.01      | v2_pre_topc(sK8)
% 19.47/3.01      | ~ l1_pre_topc(X0)
% 19.47/3.01      | sK6 != X1
% 19.47/3.01      | sK7 != X2
% 19.47/3.01      | sK5 != X0 ),
% 19.47/3.01      inference(resolution_lifted,[status(thm)],[c_18,c_43]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3508,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.01      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.01      | v2_struct_0(sK6)
% 19.47/3.01      | v2_struct_0(sK7)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | v2_pre_topc(sK8)
% 19.47/3.01      | ~ l1_pre_topc(sK5) ),
% 19.47/3.01      inference(unflattening,[status(thm)],[c_3507]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3510,plain,
% 19.47/3.01      ( v2_pre_topc(sK8)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3508,c_54,c_53,c_52,c_51,c_50,c_49,c_48]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3511,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | v2_pre_topc(sK8) ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_3510]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3586,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) | v2_pre_topc(sK8) ),
% 19.47/3.01      inference(backward_subsumption_resolution,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3561,c_3511]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3589,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_3586]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3490,plain,
% 19.47/3.01      ( ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
% 19.47/3.01      | ~ r1_tsep_1(X1,X2)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(X2,X0)
% 19.47/3.01      | ~ m1_pre_topc(X1,X0)
% 19.47/3.01      | v2_struct_0(X0)
% 19.47/3.01      | v2_struct_0(X1)
% 19.47/3.01      | v2_struct_0(X2)
% 19.47/3.01      | ~ v2_struct_0(sK8)
% 19.47/3.01      | ~ v2_pre_topc(X0)
% 19.47/3.01      | ~ l1_pre_topc(X0)
% 19.47/3.01      | sK6 != X1
% 19.47/3.01      | sK7 != X2
% 19.47/3.01      | sK5 != X0 ),
% 19.47/3.01      inference(resolution_lifted,[status(thm)],[c_18,c_44]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3491,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.01      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.01      | v2_struct_0(sK6)
% 19.47/3.01      | v2_struct_0(sK7)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | ~ v2_struct_0(sK8)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | ~ l1_pre_topc(sK5) ),
% 19.47/3.01      inference(unflattening,[status(thm)],[c_3490]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3493,plain,
% 19.47/3.01      ( ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ v2_struct_0(sK8) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3491,c_54,c_53,c_52,c_51,c_50,c_49,c_48]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3494,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ v2_struct_0(sK8) ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_3493]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3585,plain,
% 19.47/3.01      ( ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) | ~ v2_struct_0(sK8) ),
% 19.47/3.01      inference(backward_subsumption_resolution,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3561,c_3494]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3590,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK8) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_3585]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3541,plain,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | ~ sP0(sK3(X0,X1,X2),X2,X1,X0)
% 19.47/3.01      | ~ r1_tsep_1(X1,X2)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(X2,X0)
% 19.47/3.01      | ~ m1_pre_topc(X1,X0)
% 19.47/3.01      | v2_struct_0(X0)
% 19.47/3.01      | v2_struct_0(X1)
% 19.47/3.01      | v2_struct_0(X2)
% 19.47/3.01      | ~ v2_pre_topc(X0)
% 19.47/3.01      | ~ l1_pre_topc(X0)
% 19.47/3.01      | sK6 != X1
% 19.47/3.01      | sK7 != X2
% 19.47/3.01      | sK5 != X0 ),
% 19.47/3.01      inference(resolution_lifted,[status(thm)],[c_18,c_41]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3542,plain,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.01      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.01      | v2_struct_0(sK6)
% 19.47/3.01      | v2_struct_0(sK7)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | ~ l1_pre_topc(sK5) ),
% 19.47/3.01      inference(unflattening,[status(thm)],[c_3541]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3544,plain,
% 19.47/3.01      ( ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ sP1(sK8,sK5,sK7,sK6) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3542,c_54,c_53,c_52,c_51,c_50,c_49,c_48]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3545,plain,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_3544]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3575,plain,
% 19.47/3.01      ( ~ sP1(sK8,sK5,sK7,sK6) | ~ sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
% 19.47/3.01      inference(backward_subsumption_resolution,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_3561,c_3545]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_3600,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_3575]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9673,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8390]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9674,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9673]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
% 19.47/3.01      | ~ v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
% 19.47/3.01      | ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 19.47/3.01      | ~ v1_funct_1(sK4(X0,X1,X2,X3)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f81]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_299,plain,
% 19.47/3.01      ( ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0) | sP1(X0,X1,X2,X3) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25,c_36,c_35,c_34]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_300,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3) | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0) ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_299]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8379,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | ~ v5_pre_topc(sK4(X0_54,X1_54,X2_54,X3_54),X1_54,X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_300]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9672,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | ~ v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8379]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9676,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9672]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_29,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f77]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8397,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_29]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9671,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8397]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9678,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9671]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_33,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f73]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8393,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_33]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9670,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8393]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9680,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9670]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9669,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8391]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9682,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9669]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),X2,X0) ),
% 19.47/3.01      inference(cnf_transformation,[],[f79]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8399,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54),X2_54,X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_27]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9668,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8399]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9684,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9668]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_31,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),X3,X0) ),
% 19.47/3.01      inference(cnf_transformation,[],[f75]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8395,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54),X3_54,X0_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_31]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9667,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8395]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9686,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9667]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9666,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8392]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9688,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9666]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f78]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8398,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54),u1_struct_0(X2_54),u1_struct_0(X0_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_28]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9665,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8398]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9690,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9665]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_32,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0)) ),
% 19.47/3.01      inference(cnf_transformation,[],[f74]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8394,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54),u1_struct_0(X3_54),u1_struct_0(X0_54)) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_32]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9664,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8394]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9692,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9664]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) ),
% 19.47/3.01      inference(cnf_transformation,[],[f80]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8400,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_26]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9663,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8400]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9694,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9663]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30,plain,
% 19.47/3.01      ( sP1(X0,X1,X2,X3)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(X1,X0,sK4(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
% 19.47/3.01      inference(cnf_transformation,[],[f76]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8396,plain,
% 19.47/3.01      ( sP1(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(X1_54,X0_54,sK4(X0_54,X1_54,X2_54,X3_54),X3_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X0_54)))) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_30]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9662,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8396]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9696,plain,
% 19.47/3.01      ( sP1(sK8,sK5,sK7,sK6) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_9662]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_22,plain,
% 19.47/3.01      ( sP0(X0,X1,X2,X3)
% 19.47/3.01      | ~ r3_tsep_1(X3,X2,X1)
% 19.47/3.01      | ~ m1_pre_topc(X1,X3)
% 19.47/3.01      | ~ m1_pre_topc(X2,X3)
% 19.47/3.01      | v2_struct_0(X3)
% 19.47/3.01      | v2_struct_0(X2)
% 19.47/3.01      | v2_struct_0(X1)
% 19.47/3.01      | v2_struct_0(X0)
% 19.47/3.01      | ~ v2_pre_topc(X3)
% 19.47/3.01      | ~ v2_pre_topc(X0)
% 19.47/3.01      | ~ l1_pre_topc(X3)
% 19.47/3.01      | ~ l1_pre_topc(X0) ),
% 19.47/3.01      inference(cnf_transformation,[],[f60]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8403,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54)
% 19.47/3.01      | ~ r3_tsep_1(X3_54,X2_54,X1_54)
% 19.47/3.01      | ~ m1_pre_topc(X1_54,X3_54)
% 19.47/3.01      | ~ m1_pre_topc(X2_54,X3_54)
% 19.47/3.01      | v2_struct_0(X0_54)
% 19.47/3.01      | v2_struct_0(X1_54)
% 19.47/3.01      | v2_struct_0(X2_54)
% 19.47/3.01      | v2_struct_0(X3_54)
% 19.47/3.01      | ~ v2_pre_topc(X0_54)
% 19.47/3.01      | ~ v2_pre_topc(X3_54)
% 19.47/3.01      | ~ l1_pre_topc(X0_54)
% 19.47/3.01      | ~ l1_pre_topc(X3_54) ),
% 19.47/3.01      inference(subtyping,[status(esa)],[c_22]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12825,plain,
% 19.47/3.01      ( sP0(sK8,sK7,sK6,sK5)
% 19.47/3.01      | ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ m1_pre_topc(sK6,sK5)
% 19.47/3.01      | ~ m1_pre_topc(sK7,sK5)
% 19.47/3.01      | v2_struct_0(sK6)
% 19.47/3.01      | v2_struct_0(sK7)
% 19.47/3.01      | v2_struct_0(sK5)
% 19.47/3.01      | v2_struct_0(sK8)
% 19.47/3.01      | ~ v2_pre_topc(sK5)
% 19.47/3.01      | ~ v2_pre_topc(sK8)
% 19.47/3.01      | ~ l1_pre_topc(sK5)
% 19.47/3.01      | ~ l1_pre_topc(sK8) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8403]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_12862,plain,
% 19.47/3.01      ( sP0(sK8,sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK6) = iProver_top
% 19.47/3.01      | v2_struct_0(sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_12825]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13777,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK6)
% 19.47/3.01      | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9357,c_13672]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13887,plain,
% 19.47/3.01      ( l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK6)
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_13777,c_55,c_56,c_57]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13888,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK6)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK6)
% 19.47/3.01      | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_13887]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13893,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13888,c_9365]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14173,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_13893,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14174,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_14173]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14177,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13579,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14179,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13114,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15957,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_14177,c_14179]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26512,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15957,c_10571]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26717,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26512,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26721,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP1(sK3(sK5,sK6,sK7),sK5,sK7,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26717,c_9353]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26513,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15957,c_10705]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26607,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26513,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26511,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15957,c_11154]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26662,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26511,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26510,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15957,c_11519]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26667,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26510,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26725,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_26721]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26509,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15957,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26734,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26509,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14178,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13445,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14180,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_12874,c_14174]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_16357,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_14178,c_14180]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27378,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16357,c_12295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27379,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16357,c_11651]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27380,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16357,c_11226]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27381,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_16357,c_10759]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30849,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26721,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9620,c_9625,c_9715,c_10084,c_10155,c_14174,c_20956,
% 19.47/3.01                 c_26607,c_26662,c_26667,c_26717,c_26734,c_27378,c_27379,
% 19.47/3.01                 c_27380,c_27381]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30853,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10985,c_30849]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30895,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_30853,c_26734]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30899,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10527,c_30895]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30902,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_30899,c_26734]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30906,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_30902,c_10295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30935,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_30906,c_26734]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15396,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK6)) = k3_tmap_1(sK5,X1_54,X0_54,sK6,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9357,c_15381]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15429,plain,
% 19.47/3.01      ( l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,X0_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,sK5) != iProver_top
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK6)) = k3_tmap_1(sK5,X1_54,X0_54,sK6,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_15396,c_55,c_56,c_57]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15430,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK6)) = k3_tmap_1(sK5,X1_54,X0_54,sK6,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_15429]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15435,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15430,c_9365]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15499,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_15435,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_12166]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15500,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_15499]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15507,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13579,c_15500]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30975,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_30935,c_15507]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15509,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13114,c_15500]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30977,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_30935,c_15509]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_31659,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_30975,c_30977]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40666,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31659,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8423,plain,( X0_54 = X0_54 ),theory(equality) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9890,plain,
% 19.47/3.01      ( sK5 = sK5 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8423]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10152,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8410]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10159,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_10152]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8428,plain,
% 19.47/3.01      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 19.47/3.01      theory(equality) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9780,plain,
% 19.47/3.01      ( X0_54 != X1_54 | sK5 != X1_54 | sK5 = X0_54 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8428]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10276,plain,
% 19.47/3.01      ( X0_54 != sK5 | sK5 = X0_54 | sK5 != sK5 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_9780]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_10561,plain,
% 19.47/3.01      ( k1_tsep_1(sK5,sK6,sK7) != sK5
% 19.47/3.01      | sK5 = k1_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | sK5 != sK5 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_10276]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8425,plain,( X0_56 = X0_56 ),theory(equality) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_17087,plain,
% 19.47/3.01      ( u1_struct_0(sK3(sK5,sK6,sK7)) = u1_struct_0(sK3(sK5,sK6,sK7)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8425]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8431,plain,
% 19.47/3.01      ( u1_struct_0(X0_54) = u1_struct_0(X1_54) | X0_54 != X1_54 ),
% 19.47/3.01      theory(equality) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13180,plain,
% 19.47/3.01      ( u1_struct_0(sK5) = u1_struct_0(X0_54) | sK5 != X0_54 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8431]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_18315,plain,
% 19.47/3.01      ( u1_struct_0(sK5) = u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
% 19.47/3.01      | sK5 != k1_tsep_1(sK5,sK6,sK7) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_13180]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_14158,plain,
% 19.47/3.01      ( ~ sP1(sK3(sK5,sK6,sK7),sK5,X0_54,X1_54)
% 19.47/3.01      | v5_pre_topc(X0_55,sK5,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54),X0_54,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54),X1_54,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54),u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ v1_funct_1(X0_55)
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X0_54))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),X0_55,X1_54)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8389]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15475,plain,
% 19.47/3.01      ( ~ sP1(sK3(sK5,sK6,sK7),sK5,X0_54,X1_54)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),sK5,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54),X1_54,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v1_funct_2(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54),u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ m1_subset_1(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ v1_funct_1(sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X0_54))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X2_54,sK7),sK7,X2_54,sK5),X1_54)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_14158]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_20953,plain,
% 19.47/3.01      ( ~ sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK5,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),sK6,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),sK7,sK3(sK5,sK6,sK7))
% 19.47/3.01      | ~ v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | ~ m1_subset_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7)))))
% 19.47/3.01      | ~ v1_funct_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6))
% 19.47/3.01      | ~ v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7)) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_15475]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_20954,plain,
% 19.47/3.01      ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_20953]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_20956,plain,
% 19.47/3.01      ( sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_20954]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8424,plain,( X0_55 = X0_55 ),theory(equality) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_28192,plain,
% 19.47/3.01      ( sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8424]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30978,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_30935,c_15500]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_8437,plain,
% 19.47/3.01      ( ~ v1_funct_2(X0_55,X0_56,X1_56)
% 19.47/3.01      | v1_funct_2(X1_55,X2_56,X3_56)
% 19.47/3.01      | X2_56 != X0_56
% 19.47/3.01      | X3_56 != X1_56
% 19.47/3.01      | X1_55 != X0_55 ),
% 19.47/3.01      theory(equality) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13125,plain,
% 19.47/3.01      ( ~ v1_funct_2(X0_55,X0_56,X1_56)
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X1_54,sK7)))
% 19.47/3.01      | u1_struct_0(sK3(sK5,X1_54,sK7)) != X1_56
% 19.47/3.01      | u1_struct_0(sK5) != X0_56
% 19.47/3.01      | sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5) != X0_55 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_8437]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_17409,plain,
% 19.47/3.01      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_54),X0_56)
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X2_54,sK7)))
% 19.47/3.01      | u1_struct_0(sK3(sK5,X2_54,sK7)) != X0_56
% 19.47/3.01      | u1_struct_0(sK5) != u1_struct_0(X0_54)
% 19.47/3.01      | sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5) != X0_55 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_13125]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26334,plain,
% 19.47/3.01      ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),X0_56)
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X1_54,sK7)))
% 19.47/3.01      | u1_struct_0(sK3(sK5,X1_54,sK7)) != X0_56
% 19.47/3.01      | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
% 19.47/3.01      | sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5) != X0_55 ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_17409]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_33466,plain,
% 19.47/3.01      ( v1_funct_2(sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X1_54,sK7)))
% 19.47/3.01      | ~ v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7)))
% 19.47/3.01      | u1_struct_0(sK3(sK5,X1_54,sK7)) != u1_struct_0(sK3(sK5,sK6,sK7))
% 19.47/3.01      | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
% 19.47/3.01      | sK2(sK3(sK5,X0_54,sK7),sK7,X0_54,sK5) != sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_26334]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_33467,plain,
% 19.47/3.01      ( u1_struct_0(sK3(sK5,X0_54,sK7)) != u1_struct_0(sK3(sK5,sK6,sK7))
% 19.47/3.01      | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
% 19.47/3.01      | sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5) != sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,X1_54,sK7),sK7,X1_54,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,X0_54,sK7))) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_33466]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_33469,plain,
% 19.47/3.01      ( u1_struct_0(sK3(sK5,sK6,sK7)) != u1_struct_0(sK3(sK5,sK6,sK7))
% 19.47/3.01      | u1_struct_0(sK5) != u1_struct_0(k1_tsep_1(sK5,sK6,sK7))
% 19.47/3.01      | sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(k1_tsep_1(sK5,sK6,sK7)),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_33467]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15508,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13445,c_15500]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30974,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_30935,c_15508]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15510,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_12874,c_15500]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_30976,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_30935,c_15510]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_31190,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_30974,c_30976]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39494,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31190,c_10759]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39513,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_39494,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39493,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31190,c_11226]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39519,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_39493,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39492,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31190,c_11651]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39560,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_39492,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39491,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31190,c_12295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39565,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_39491,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40670,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31659,c_10705]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40677,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40670,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40668,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31659,c_11154]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40708,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40668,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40667,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31659,c_11519]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40713,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40667,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40669,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_31659,c_10571]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40739,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40669,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40840,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40666,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_8387,c_9620,c_9625,c_9715,c_9720,c_9890,c_10084,
% 19.47/3.01                 c_10155,c_10159,c_10561,c_17087,c_18315,c_20956,c_28192,
% 19.47/3.01                 c_30978,c_33469,c_39513,c_39519,c_39560,c_39565,c_40677,
% 19.47/3.01                 c_40708,c_40713,c_40739]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40844,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10985,c_40840]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40926,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40844,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40930,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_40926,c_10295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40933,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_40930,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_30978]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13776,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK7)
% 19.47/3.01      | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9355,c_13672]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13789,plain,
% 19.47/3.01      ( l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK7)
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_13776,c_55,c_56,c_57]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13790,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(X0_54),sK4(X0_54,sK5,X1_54,X2_54),u1_struct_0(sK7)) = k2_tmap_1(sK5,X0_54,sK4(X0_54,sK5,X1_54,X2_54),sK7)
% 19.47/3.01      | sP1(X0_54,sK5,X1_54,X2_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_13789]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13795,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13790,c_9365]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13896,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_13795,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13897,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_13896]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13900,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13579,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13902,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13114,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15921,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13900,c_13902]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25681,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15921,c_10571]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25855,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25681,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25859,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP1(sK3(sK5,sK6,sK7),sK5,sK7,X0_54) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_25855,c_9353]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25682,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15921,c_10705]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25777,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25682,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25680,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15921,c_11154]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25782,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25680,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25679,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15921,c_11519]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25850,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25679,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25863,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP1(sK3(sK5,sK6,sK7),sK5,sK7,sK6) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.01      inference(instantiation,[status(thm)],[c_25859]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25678,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15921,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_25934,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25678,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13901,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13445,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_13903,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_12874,c_13897]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15952,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13901,c_13903]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26137,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15952,c_12295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26138,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15952,c_11651]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26139,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15952,c_11226]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26140,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15952,c_10759]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26394,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_25859,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9620,c_9625,c_9715,c_10084,c_10155,c_13897,c_25777,
% 19.47/3.01                 c_25782,c_25850,c_25863,c_25934,c_26137,c_26138,c_26139,
% 19.47/3.01                 c_26140]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26398,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10985,c_26394]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26401,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26398,c_25934]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26405,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10527,c_26401]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26503,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26405,c_25934]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26507,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26503,c_10295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26560,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_26507,c_25934]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15395,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK7)) = k3_tmap_1(sK5,X1_54,X0_54,sK7,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9355,c_15381]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15406,plain,
% 19.47/3.01      ( l1_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,X0_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,sK5) != iProver_top
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK7)) = k3_tmap_1(sK5,X1_54,X0_54,sK7,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_15395,c_55,c_56,c_57]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15407,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4(X1_54,X0_54,X2_54,X3_54),u1_struct_0(sK7)) = k3_tmap_1(sK5,X1_54,X0_54,sK7,sK4(X1_54,X0_54,X2_54,X3_54))
% 19.47/3.01      | sP1(X1_54,X0_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | m1_pre_topc(X0_54,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,X0_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X1_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X1_54) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_15406]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15412,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK8) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK8) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK8) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_15407,c_9365]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15482,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_15412,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.01                 c_68,c_3560,c_12166]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15483,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6))
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(renaming,[status(thm)],[c_15482]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15490,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13579,c_15483]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26593,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_26560,c_15490]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15492,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13114,c_15483]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26595,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_26560,c_15492]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_27549,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.01      | k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26593,c_26595]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38864,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_27549,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26596,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_26560,c_15483]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15491,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_13445,c_15483]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26592,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_26560,c_15491]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_15493,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK8),sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_12874,c_15483]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26594,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_26560,c_15493]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_26982,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.01      | k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26592,c_26594]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36249,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26982,c_10759]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36373,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_36249,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36248,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26982,c_11226]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36378,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_36248,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36247,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26982,c_11651]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36477,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_36247,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36246,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_26982,c_12295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_36482,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_36246,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38868,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_27549,c_10705]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38946,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_38868,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38866,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_27549,c_11154]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38951,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_38866,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38865,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_27549,c_11519]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39027,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_38865,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_38867,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_27549,c_10571]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39032,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_38867,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39092,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_38864,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_8387,c_9620,c_9625,c_9715,c_9720,c_9890,c_10084,
% 19.47/3.01                 c_10155,c_10159,c_10561,c_17087,c_18315,c_20956,c_26596,
% 19.47/3.01                 c_28192,c_33469,c_36373,c_36378,c_36477,c_36482,c_38946,
% 19.47/3.01                 c_38951,c_39027,c_39032]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39096,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_10985,c_39092]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39099,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_39096,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39103,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)
% 19.47/3.01      | sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_39099,c_10295]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39196,plain,
% 19.47/3.01      ( k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)) = k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7) ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_39103,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_9720,c_26596]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39198,plain,
% 19.47/3.01      ( sP0(sK8,sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),sK6,sK8) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)),sK7,sK8) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) = iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),u1_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK8,sK5,sK7,sK4(sK8,sK5,sK7,sK6))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_39196,c_10489]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_39199,plain,
% 19.47/3.01      ( sP0(sK8,sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),sK6,sK8) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) != iProver_top
% 19.47/3.01      | v1_funct_2(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),u1_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | m1_subset_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | v1_funct_1(k3_tmap_1(sK5,sK8,sK5,sK6,sK4(sK8,sK5,sK7,sK6))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) != iProver_top ),
% 19.47/3.01      inference(light_normalisation,[status(thm)],[c_39198,c_39196]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_40935,plain,
% 19.47/3.01      ( sP0(sK8,sK7,sK6,sK5) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) = iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) != iProver_top
% 19.47/3.01      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) != iProver_top
% 19.47/3.01      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top
% 19.47/3.01      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) != iProver_top
% 19.47/3.01      | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) != iProver_top
% 19.47/3.01      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) != iProver_top ),
% 19.47/3.01      inference(demodulation,[status(thm)],[c_40933,c_39199]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_42579,plain,
% 19.47/3.01      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) != iProver_top ),
% 19.47/3.01      inference(global_propositional_subsumption,
% 19.47/3.01                [status(thm)],
% 19.47/3.01                [c_42280,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.01                 c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,
% 19.47/3.01                 c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,
% 19.47/3.01                 c_9720,c_12862,c_40935]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_42597,plain,
% 19.47/3.01      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.01      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_11504,c_42579]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_9339,plain,
% 19.47/3.01      ( sP0(X0_54,X1_54,X2_54,X3_54) = iProver_top
% 19.47/3.01      | r3_tsep_1(X3_54,X2_54,X1_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 19.47/3.01      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 19.47/3.01      | v2_struct_0(X0_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X1_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X2_54) = iProver_top
% 19.47/3.01      | v2_struct_0(X3_54) = iProver_top
% 19.47/3.01      | v2_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | v2_pre_topc(X3_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X0_54) != iProver_top
% 19.47/3.01      | l1_pre_topc(X3_54) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_8403]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_42583,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK6,sK5) != iProver_top
% 19.47/3.01      | m1_pre_topc(sK7,sK5) != iProver_top
% 19.47/3.01      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.01      | v2_struct_0(sK6) = iProver_top
% 19.47/3.01      | v2_struct_0(sK7) = iProver_top
% 19.47/3.01      | v2_struct_0(sK5) = iProver_top
% 19.47/3.01      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | v2_pre_topc(sK5) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.01      | l1_pre_topc(sK5) != iProver_top ),
% 19.47/3.01      inference(superposition,[status(thm)],[c_9339,c_42579]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_1641,plain,
% 19.47/3.01      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ v5_pre_topc(sK4(X0,X1,X2,X3),X1,X0)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | sK6 != X3
% 19.47/3.01      | sK7 != X2
% 19.47/3.01      | sK5 != X1
% 19.47/3.01      | sK8 != X0 ),
% 19.47/3.01      inference(resolution_lifted,[status(thm)],[c_300,c_41]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_1642,plain,
% 19.47/3.01      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.01      inference(unflattening,[status(thm)],[c_1641]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_1643,plain,
% 19.47/3.01      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.01      | v5_pre_topc(sK4(sK8,sK5,sK7,sK6),sK5,sK8) != iProver_top
% 19.47/3.01      | r1_tsep_1(sK6,sK7) != iProver_top ),
% 19.47/3.01      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 19.47/3.01  
% 19.47/3.01  cnf(c_1654,plain,
% 19.47/3.01      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.01      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.01      | v1_funct_1(sK4(X0,X1,X2,X3))
% 19.47/3.01      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X1
% 19.47/3.02      | sK8 != X0 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_36,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1655,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1654]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1656,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.02      | v1_funct_1(sK4(sK8,sK5,sK7,sK6)) = iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1667,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v1_funct_2(sK4(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X1
% 19.47/3.02      | sK8 != X0 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_35,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1668,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8))
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1667]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1669,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | v1_funct_2(sK4(sK8,sK5,sK7,sK6),u1_struct_0(sK5),u1_struct_0(sK8)) = iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1680,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X1
% 19.47/3.02      | sK8 != X0 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_34,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1681,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1680]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1682,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.02      | m1_subset_1(sK4(sK8,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK8)))) = iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1693,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | v1_funct_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3))
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1694,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1693]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1695,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6)) = iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1694]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1706,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v1_funct_2(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X1))
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_32,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1707,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8))
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1706]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1708,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),u1_struct_0(sK6),u1_struct_0(sK8)) = iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1707]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1719,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3),X3,X1)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_31,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1720,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1719]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1721,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),sK6,sK8) = iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1720]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1732,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | m1_subset_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1733,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1732]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1734,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK8)))) = iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1733]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1745,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | v1_funct_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2))
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1746,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1745]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1747,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7)) = iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1746]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1758,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v1_funct_2(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X1))
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1759,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8))
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1758]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1760,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1771,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2),X2,X1)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_27,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1772,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1771]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1773,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),sK7,sK8) = iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1772]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1784,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | m1_subset_1(k2_tmap_1(X0,X1,sK4(X1,X0,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 19.47/3.02      | sK6 != X3
% 19.47/3.02      | sK7 != X2
% 19.47/3.02      | sK5 != X0
% 19.47/3.02      | sK8 != X1 ),
% 19.47/3.02      inference(resolution_lifted,[status(thm)],[c_26,c_41]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1785,plain,
% 19.47/3.02      ( ~ r3_tsep_1(sK5,sK6,sK7)
% 19.47/3.02      | ~ r1_tsep_1(sK6,sK7)
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) ),
% 19.47/3.02      inference(unflattening,[status(thm)],[c_1784]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_1786,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | r1_tsep_1(sK6,sK7) != iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK8,sK4(sK8,sK5,sK7,sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK8)))) = iProver_top ),
% 19.47/3.02      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43087,plain,
% 19.47/3.02      ( r3_tsep_1(sK5,sK6,sK7) != iProver_top ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_42583,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.02                 c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,
% 19.47/3.02                 c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_12862,
% 19.47/3.02                 c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44314,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_42597,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.02                 c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,
% 19.47/3.02                 c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_9620,c_9625,
% 19.47/3.02                 c_9715,c_12166,c_12743,c_12862,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_42599,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)
% 19.47/3.02      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_11346,c_42579]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_42889,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK7)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_42599,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.02                 c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,
% 19.47/3.02                 c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_12862,
% 19.47/3.02                 c_13114,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44316,plain,
% 19.47/3.02      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK7,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7) ),
% 19.47/3.02      inference(light_normalisation,[status(thm)],[c_44314,c_42889]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44336,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_44316,c_10571]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44485,plain,
% 19.47/3.02      ( m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_44336,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.02                 c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,
% 19.47/3.02                 c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,
% 19.47/3.02                 c_9720,c_12862,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_42596,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5))
% 19.47/3.02      | m1_pre_topc(sK5,sK5) != iProver_top
% 19.47/3.02      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_11779,c_42579]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43315,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_42596,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.02                 c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,
% 19.47/3.02                 c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_9620,c_9625,
% 19.47/3.02                 c_9715,c_12166,c_12742,c_12862,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_42598,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)
% 19.47/3.02      | v2_struct_0(sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | v2_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | l1_pre_topc(sK3(sK5,sK6,sK7)) != iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_11347,c_42579]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_42839,plain,
% 19.47/3.02      ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7)),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK6)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_42598,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.02                 c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,
% 19.47/3.02                 c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_12862,
% 19.47/3.02                 c_12874,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43317,plain,
% 19.47/3.02      ( k3_tmap_1(sK5,sK3(sK5,sK6,sK7),sK5,sK6,sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) = k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6) ),
% 19.47/3.02      inference(light_normalisation,[status(thm)],[c_43315,c_42839]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43337,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_43317,c_12295]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43755,plain,
% 19.47/3.02      ( m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))))) = iProver_top ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_43337,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.02                 c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,
% 19.47/3.02                 c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,
% 19.47/3.02                 c_9720,c_12862,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43759,plain,
% 19.47/3.02      ( sP1(sK3(sK5,sK6,sK7),sK5,sK6,X0_54) != iProver_top
% 19.47/3.02      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | v1_funct_2(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.02      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | v1_funct_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5)) != iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) != iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_43755,c_9353]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43338,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),u1_struct_0(sK6),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_43317,c_11651]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43339,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6),sK6,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_43317,c_11226]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43340,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK6)) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_43317,c_10759]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43771,plain,
% 19.47/3.02      ( v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | sP1(sK3(sK5,sK6,sK7),sK5,sK6,X0_54) != iProver_top
% 19.47/3.02      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_43759,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.02                 c_3588,c_3589,c_3590,c_3600,c_8387,c_9674,c_9676,c_9678,
% 19.47/3.02                 c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,
% 19.47/3.02                 c_9696,c_9720,c_9890,c_10155,c_10159,c_10561,c_12862,
% 19.47/3.02                 c_17087,c_18315,c_28192,c_33469,c_40935,c_43338,c_43339,
% 19.47/3.02                 c_43340]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_43772,plain,
% 19.47/3.02      ( sP1(sK3(sK5,sK6,sK7),sK5,sK6,X0_54) != iProver_top
% 19.47/3.02      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),X0_54,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.02      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | m1_subset_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),X0_54)) != iProver_top ),
% 19.47/3.02      inference(renaming,[status(thm)],[c_43771]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44492,plain,
% 19.47/3.02      ( sP1(sK3(sK5,sK6,sK7),sK5,sK6,sK7) != iProver_top
% 19.47/3.02      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) != iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) != iProver_top
% 19.47/3.02      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) != iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_44485,c_43772]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44334,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v1_funct_2(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),u1_struct_0(sK7),u1_struct_0(sK3(sK5,sK6,sK7))) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_44316,c_11519]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44335,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v5_pre_topc(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7),sK7,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_44316,c_11154]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44337,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v1_funct_1(k2_tmap_1(sK5,sK3(sK5,sK6,sK7),sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK7)) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_44316,c_10705]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44578,plain,
% 19.47/3.02      ( m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top
% 19.47/3.02      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_44492,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_66,c_67,
% 19.47/3.02                 c_68,c_1643,c_1656,c_1669,c_1682,c_1695,c_1708,c_1721,
% 19.47/3.02                 c_1734,c_1747,c_1760,c_1773,c_1786,c_3560,c_3588,c_3589,
% 19.47/3.02                 c_3590,c_3600,c_8387,c_9620,c_9625,c_9674,c_9676,c_9678,
% 19.47/3.02                 c_9680,c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,
% 19.47/3.02                 c_9696,c_9715,c_9720,c_9890,c_10084,c_10155,c_10159,
% 19.47/3.02                 c_10561,c_12862,c_17087,c_18315,c_20956,c_28192,c_33469,
% 19.47/3.02                 c_40935,c_43337,c_43338,c_43339,c_43340,c_44334,c_44335,
% 19.47/3.02                 c_44336,c_44337]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44579,plain,
% 19.47/3.02      ( v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top
% 19.47/3.02      | m1_subset_1(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK5,sK6,sK7))))) != iProver_top ),
% 19.47/3.02      inference(renaming,[status(thm)],[c_44578]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44582,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top
% 19.47/3.02      | v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_10985,c_44579]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44656,plain,
% 19.47/3.02      ( v5_pre_topc(sK2(sK3(sK5,sK6,sK7),sK7,sK6,sK5),sK5,sK3(sK5,sK6,sK7)) = iProver_top ),
% 19.47/3.02      inference(global_propositional_subsumption,
% 19.47/3.02                [status(thm)],
% 19.47/3.02                [c_44582,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3560,
% 19.47/3.02                 c_3588,c_3589,c_3590,c_3600,c_9674,c_9676,c_9678,c_9680,
% 19.47/3.02                 c_9682,c_9684,c_9686,c_9688,c_9690,c_9692,c_9694,c_9696,
% 19.47/3.02                 c_9720,c_12862,c_40935]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(c_44660,plain,
% 19.47/3.02      ( sP0(sK3(sK5,sK6,sK7),sK7,sK6,sK5) = iProver_top ),
% 19.47/3.02      inference(superposition,[status(thm)],[c_44656,c_10295]) ).
% 19.47/3.02  
% 19.47/3.02  cnf(contradiction,plain,
% 19.47/3.02      ( $false ),
% 19.47/3.02      inference(minisat,[status(thm)],[c_44660,c_42579]) ).
% 19.47/3.02  
% 19.47/3.02  
% 19.47/3.02  % SZS output end CNFRefutation for theBenchmark.p
% 19.47/3.02  
% 19.47/3.02  ------                               Statistics
% 19.47/3.02  
% 19.47/3.02  ------ General
% 19.47/3.02  
% 19.47/3.02  abstr_ref_over_cycles:                  0
% 19.47/3.02  abstr_ref_under_cycles:                 0
% 19.47/3.02  gc_basic_clause_elim:                   0
% 19.47/3.02  forced_gc_time:                         0
% 19.47/3.02  parsing_time:                           0.013
% 19.47/3.02  unif_index_cands_time:                  0.
% 19.47/3.02  unif_index_add_time:                    0.
% 19.47/3.02  orderings_time:                         0.
% 19.47/3.02  out_proof_time:                         0.17
% 19.47/3.02  total_time:                             2.161
% 19.47/3.02  num_of_symbols:                         59
% 19.47/3.02  num_of_terms:                           38082
% 19.47/3.02  
% 19.47/3.02  ------ Preprocessing
% 19.47/3.02  
% 19.47/3.02  num_of_splits:                          0
% 19.47/3.02  num_of_split_atoms:                     0
% 19.47/3.02  num_of_reused_defs:                     0
% 19.47/3.02  num_eq_ax_congr_red:                    66
% 19.47/3.02  num_of_sem_filtered_clauses:            1
% 19.47/3.02  num_of_subtypes:                        5
% 19.47/3.02  monotx_restored_types:                  0
% 19.47/3.02  sat_num_of_epr_types:                   0
% 19.47/3.02  sat_num_of_non_cyclic_types:            0
% 19.47/3.02  sat_guarded_non_collapsed_types:        0
% 19.47/3.02  num_pure_diseq_elim:                    0
% 19.47/3.02  simp_replaced_by:                       0
% 19.47/3.02  res_preprocessed:                       249
% 19.47/3.02  prep_upred:                             0
% 19.47/3.02  prep_unflattend:                        499
% 19.47/3.02  smt_new_axioms:                         0
% 19.47/3.02  pred_elim_cands:                        12
% 19.47/3.02  pred_elim:                              0
% 19.47/3.02  pred_elim_cl:                           0
% 19.47/3.02  pred_elim_cycles:                       11
% 19.47/3.02  merged_defs:                            0
% 19.47/3.02  merged_defs_ncl:                        0
% 19.47/3.02  bin_hyper_res:                          0
% 19.47/3.02  prep_cycles:                            4
% 19.47/3.02  pred_elim_time:                         0.128
% 19.47/3.02  splitting_time:                         0.
% 19.47/3.02  sem_filter_time:                        0.
% 19.47/3.02  monotx_time:                            0.
% 19.47/3.02  subtype_inf_time:                       0.
% 19.47/3.02  
% 19.47/3.02  ------ Problem properties
% 19.47/3.02  
% 19.47/3.02  clauses:                                49
% 19.47/3.02  conjectures:                            9
% 19.47/3.02  epr:                                    16
% 19.47/3.02  horn:                                   18
% 19.47/3.02  ground:                                 13
% 19.47/3.02  unary:                                  9
% 19.47/3.02  binary:                                 29
% 19.47/3.02  lits:                                   183
% 19.47/3.02  lits_eq:                                3
% 19.47/3.02  fd_pure:                                0
% 19.47/3.02  fd_pseudo:                              0
% 19.47/3.02  fd_cond:                                0
% 19.47/3.02  fd_pseudo_cond:                         0
% 19.47/3.02  ac_symbols:                             0
% 19.47/3.02  
% 19.47/3.02  ------ Propositional Solver
% 19.47/3.02  
% 19.47/3.02  prop_solver_calls:                      47
% 19.47/3.02  prop_fast_solver_calls:                 10749
% 19.47/3.02  smt_solver_calls:                       0
% 19.47/3.02  smt_fast_solver_calls:                  0
% 19.47/3.02  prop_num_of_clauses:                    17197
% 19.47/3.02  prop_preprocess_simplified:             43566
% 19.47/3.02  prop_fo_subsumed:                       1583
% 19.47/3.02  prop_solver_time:                       0.
% 19.47/3.02  smt_solver_time:                        0.
% 19.47/3.02  smt_fast_solver_time:                   0.
% 19.47/3.02  prop_fast_solver_time:                  0.
% 19.47/3.02  prop_unsat_core_time:                   0.001
% 19.47/3.02  
% 19.47/3.02  ------ QBF
% 19.47/3.02  
% 19.47/3.02  qbf_q_res:                              0
% 19.47/3.02  qbf_num_tautologies:                    0
% 19.47/3.02  qbf_prep_cycles:                        0
% 19.47/3.02  
% 19.47/3.02  ------ BMC1
% 19.47/3.02  
% 19.47/3.02  bmc1_current_bound:                     -1
% 19.47/3.02  bmc1_last_solved_bound:                 -1
% 19.47/3.02  bmc1_unsat_core_size:                   -1
% 19.47/3.02  bmc1_unsat_core_parents_size:           -1
% 19.47/3.02  bmc1_merge_next_fun:                    0
% 19.47/3.02  bmc1_unsat_core_clauses_time:           0.
% 19.47/3.02  
% 19.47/3.02  ------ Instantiation
% 19.47/3.02  
% 19.47/3.02  inst_num_of_clauses:                    1209
% 19.47/3.02  inst_num_in_passive:                    161
% 19.47/3.02  inst_num_in_active:                     3651
% 19.47/3.02  inst_num_in_unprocessed:                151
% 19.47/3.02  inst_num_of_loops:                      3909
% 19.47/3.02  inst_num_of_learning_restarts:          1
% 19.47/3.02  inst_num_moves_active_passive:          246
% 19.47/3.02  inst_lit_activity:                      0
% 19.47/3.02  inst_lit_activity_moves:                2
% 19.47/3.02  inst_num_tautologies:                   0
% 19.47/3.02  inst_num_prop_implied:                  0
% 19.47/3.02  inst_num_existing_simplified:           0
% 19.47/3.02  inst_num_eq_res_simplified:             0
% 19.47/3.02  inst_num_child_elim:                    0
% 19.47/3.02  inst_num_of_dismatching_blockings:      2368
% 19.47/3.02  inst_num_of_non_proper_insts:           5918
% 19.47/3.02  inst_num_of_duplicates:                 0
% 19.47/3.02  inst_inst_num_from_inst_to_res:         0
% 19.47/3.02  inst_dismatching_checking_time:         0.
% 19.47/3.02  
% 19.47/3.02  ------ Resolution
% 19.47/3.02  
% 19.47/3.02  res_num_of_clauses:                     75
% 19.47/3.02  res_num_in_passive:                     75
% 19.47/3.02  res_num_in_active:                      0
% 19.47/3.02  res_num_of_loops:                       253
% 19.47/3.02  res_forward_subset_subsumed:            137
% 19.47/3.02  res_backward_subset_subsumed:           2
% 19.47/3.02  res_forward_subsumed:                   0
% 19.47/3.02  res_backward_subsumed:                  1
% 19.47/3.02  res_forward_subsumption_resolution:     0
% 19.47/3.02  res_backward_subsumption_resolution:    24
% 19.47/3.02  res_clause_to_clause_subsumption:       3667
% 19.47/3.02  res_orphan_elimination:                 0
% 19.47/3.02  res_tautology_del:                      383
% 19.47/3.02  res_num_eq_res_simplified:              0
% 19.47/3.02  res_num_sel_changes:                    0
% 19.47/3.02  res_moves_from_active_to_pass:          0
% 19.47/3.02  
% 19.47/3.02  ------ Superposition
% 19.47/3.02  
% 19.47/3.02  sup_time_total:                         0.
% 19.47/3.02  sup_time_generating:                    0.
% 19.47/3.02  sup_time_sim_full:                      0.
% 19.47/3.02  sup_time_sim_immed:                     0.
% 19.47/3.02  
% 19.47/3.02  sup_num_of_clauses:                     604
% 19.47/3.02  sup_num_in_active:                      237
% 19.47/3.02  sup_num_in_passive:                     367
% 19.47/3.02  sup_num_of_loops:                       780
% 19.47/3.02  sup_fw_superposition:                   1093
% 19.47/3.02  sup_bw_superposition:                   570
% 19.47/3.02  sup_immediate_simplified:               174
% 19.47/3.02  sup_given_eliminated:                   15
% 19.47/3.02  comparisons_done:                       0
% 19.47/3.02  comparisons_avoided:                    846
% 19.47/3.02  
% 19.47/3.02  ------ Simplifications
% 19.47/3.02  
% 19.47/3.02  
% 19.47/3.02  sim_fw_subset_subsumed:                 78
% 19.47/3.02  sim_bw_subset_subsumed:                 321
% 19.47/3.02  sim_fw_subsumed:                        48
% 19.47/3.02  sim_bw_subsumed:                        158
% 19.47/3.02  sim_fw_subsumption_res:                 0
% 19.47/3.02  sim_bw_subsumption_res:                 0
% 19.47/3.02  sim_tautology_del:                      22
% 19.47/3.02  sim_eq_tautology_del:                   83
% 19.47/3.02  sim_eq_res_simp:                        0
% 19.47/3.02  sim_fw_demodulated:                     0
% 19.47/3.02  sim_bw_demodulated:                     184
% 19.47/3.02  sim_light_normalised:                   56
% 19.47/3.02  sim_joinable_taut:                      0
% 19.47/3.02  sim_joinable_simp:                      0
% 19.47/3.02  sim_ac_normalised:                      0
% 19.47/3.02  sim_smt_subsumption:                    0
% 19.47/3.02  
%------------------------------------------------------------------------------
