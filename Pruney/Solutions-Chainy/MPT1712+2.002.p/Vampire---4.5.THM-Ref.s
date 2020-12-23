%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 420 expanded)
%              Number of leaves         :   37 ( 245 expanded)
%              Depth                    :   15
%              Number of atoms          : 1034 (4579 expanded)
%              Number of equality atoms :   60 ( 570 expanded)
%              Maximal formula depth    :   39 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f108,f112,f116,f120,f125,f130,f135,f140,f167,f171,f182,f184,f187])).

fof(f187,plain,
    ( spl9_14
    | spl9_11
    | ~ spl9_10
    | spl9_9
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f186,f150,f110,f94,f98,f102,f106,f118])).

fof(f118,plain,
    ( spl9_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f106,plain,
    ( spl9_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f102,plain,
    ( spl9_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f98,plain,
    ( spl9_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f94,plain,
    ( spl9_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f110,plain,
    ( spl9_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f150,plain,
    ( spl9_19
  <=> ! [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ spl9_19 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_19 ),
    inference(resolution,[],[f151,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f151,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f184,plain,
    ( spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | spl9_11
    | ~ spl9_10
    | spl9_9
    | ~ spl9_8
    | ~ spl9_7
    | ~ spl9_18
    | ~ spl9_17
    | ~ spl9_15
    | ~ spl9_16
    | spl9_22 ),
    inference(avatar_split_clause,[],[f183,f180,f128,f123,f133,f138,f90,f94,f98,f102,f106,f110,f114,f118])).

fof(f114,plain,
    ( spl9_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f90,plain,
    ( spl9_7
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f138,plain,
    ( spl9_18
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f133,plain,
    ( spl9_17
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f123,plain,
    ( spl9_15
  <=> m1_connsp_2(sK6,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f128,plain,
    ( spl9_16
  <=> m1_connsp_2(sK7,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f180,plain,
    ( spl9_22
  <=> r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f183,plain,
    ( ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_22 ),
    inference(resolution,[],[f181,f60])).

fof(f60,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK8(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK8(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X3,sK8(X0,X1,X2,X3,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tarski(sK8(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
                                    & r2_hidden(X3,sK8(X0,X1,X2,X3,X6,X7))
                                    & v3_pre_topc(sK8(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
                                    & m1_subset_1(sK8(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f30])).

fof(f30,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK8(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
        & r2_hidden(X3,sK8(X0,X1,X2,X3,X6,X7))
        & v3_pre_topc(sK8(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & r2_hidden(X3,X8)
                                        & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tmap_1)).

fof(f181,plain,
    ( ~ r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7))
    | spl9_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( ~ spl9_16
    | spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | spl9_11
    | ~ spl9_10
    | spl9_9
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_17
    | ~ spl9_15
    | ~ spl9_7
    | ~ spl9_22
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f175,f157,f128,f123,f180,f90,f123,f133,f138,f94,f98,f102,f106,f110,f114,f118,f128])).

fof(f157,plain,
    ( spl9_21
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,X2))
        | ~ m1_connsp_2(X2,sK2,sK3)
        | ~ m1_connsp_2(X1,sK1,sK3)
        | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,X2),k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f175,plain,
    ( ~ r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ~ r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(resolution,[],[f173,f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(sK8(X3,X2,X0,X1,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),sK3)
      | ~ m1_connsp_2(sK6,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X3,X2,X0)))
      | ~ m1_pre_topc(X0,X3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_connsp_2(sK7,X0,X1) ) ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
        | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
    & m1_connsp_2(sK7,sK2,sK5)
    & m1_connsp_2(sK6,sK1,sK4)
    & sK3 = sK5
    & sK3 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f28,f27,f26,f25,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ! [X8] :
                                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                        | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                    & m1_connsp_2(X7,X2,X5) )
                                & m1_connsp_2(X6,X1,X4) )
                            & X3 = X5
                            & X3 = X4
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
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
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,X1,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,X2),X3) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,sK1,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,X2),X3) )
                            & m1_connsp_2(X7,X2,X5) )
                        & m1_connsp_2(X6,sK1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),X3) )
                          & m1_connsp_2(X7,sK2,X5) )
                      & m1_connsp_2(X6,sK1,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(sK2)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),X3) )
                        & m1_connsp_2(X7,sK2,X5) )
                    & m1_connsp_2(X6,sK1,X4) )
                & X3 = X5
                & X3 = X4
                & m1_subset_1(X5,u1_struct_0(sK2)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                      & m1_connsp_2(X7,sK2,X5) )
                  & m1_connsp_2(X6,sK1,X4) )
              & sK3 = X5
              & sK3 = X4
              & m1_subset_1(X5,u1_struct_0(sK2)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                    & m1_connsp_2(X7,sK2,X5) )
                & m1_connsp_2(X6,sK1,X4) )
            & sK3 = X5
            & sK3 = X4
            & m1_subset_1(X5,u1_struct_0(sK2)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                  & m1_connsp_2(X7,sK2,X5) )
              & m1_connsp_2(X6,sK1,sK4) )
          & sK3 = X5
          & sK3 = sK4
          & m1_subset_1(X5,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                & m1_connsp_2(X7,sK2,X5) )
            & m1_connsp_2(X6,sK1,sK4) )
        & sK3 = X5
        & sK3 = sK4
        & m1_subset_1(X5,u1_struct_0(sK2)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
              & m1_connsp_2(X7,sK2,sK5) )
          & m1_connsp_2(X6,sK1,sK4) )
      & sK3 = sK5
      & sK3 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
            & m1_connsp_2(X7,sK2,sK5) )
        & m1_connsp_2(X6,sK1,sK4) )
   => ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
              | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
          & m1_connsp_2(X7,sK2,sK5) )
      & m1_connsp_2(sK6,sK1,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X7] :
        ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
            | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
        & m1_connsp_2(X7,sK2,sK5) )
   => ( ! [X8] :
          ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
          | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
      & m1_connsp_2(sK7,sK2,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X3 = X4 )
                             => ! [X6] :
                                  ( m1_connsp_2(X6,X1,X4)
                                 => ! [X7] :
                                      ( m1_connsp_2(X7,X2,X5)
                                     => ? [X8] :
                                          ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                          & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tmap_1)).

fof(f58,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK8(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK8(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tarski(sK8(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f173,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK8(sK0,sK1,sK2,sK3,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,sK6,sK7))
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(resolution,[],[f172,f124])).

fof(f124,plain,
    ( m1_connsp_2(sK6,sK1,sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X1,sK1,sK3)
        | ~ r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,sK7))
        | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,sK7),k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(resolution,[],[f158,f129])).

fof(f129,plain,
    ( m1_connsp_2(sK7,sK2,sK3)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X2,sK2,sK3)
        | ~ r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,X2))
        | ~ m1_connsp_2(X1,sK1,sK3)
        | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,X2),k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f171,plain,
    ( spl9_14
    | ~ spl9_12
    | spl9_11
    | ~ spl9_10
    | spl9_9
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f169,f153,f94,f98,f102,f106,f110,f118])).

fof(f153,plain,
    ( spl9_20
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f169,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_20 ),
    inference(resolution,[],[f154,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f154,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f167,plain,
    ( spl9_19
    | spl9_20
    | ~ spl9_17
    | spl9_21
    | spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | spl9_11
    | ~ spl9_10
    | spl9_9
    | ~ spl9_8
    | ~ spl9_18
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f148,f90,f138,f94,f98,f102,f106,f110,f114,f118,f157,f133,f153,f150])).

fof(f148,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,X2))
        | ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,X2),k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_connsp_2(X1,sK1,sK3)
        | ~ m1_connsp_2(X2,sK2,sK3)
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl9_7 ),
    inference(resolution,[],[f147,f91])).

fof(f91,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f147,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(X2,X1,X3)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ r2_hidden(X4,sK8(X2,X1,X3,X0,X5,X6))
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X1,X3)))
      | m1_connsp_2(sK8(X2,X1,X3,X0,X5,X6),k1_tsep_1(X2,X1,X3),X4)
      | ~ m1_connsp_2(X5,X1,X0)
      | ~ m1_connsp_2(X6,X3,X0)
      | v2_struct_0(k1_tsep_1(X2,X1,X3))
      | ~ m1_pre_topc(k1_tsep_1(X2,X1,X3),X7)
      | ~ l1_pre_topc(X7) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(X2,X1,X3)))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ r2_hidden(X4,sK8(X2,X1,X3,X0,X5,X6))
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X1,X3)))
      | m1_connsp_2(sK8(X2,X1,X3,X0,X5,X6),k1_tsep_1(X2,X1,X3),X4)
      | ~ m1_connsp_2(X5,X1,X0)
      | ~ m1_connsp_2(X6,X3,X0)
      | v2_struct_0(k1_tsep_1(X2,X1,X3))
      | ~ m1_pre_topc(k1_tsep_1(X2,X1,X3),X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_connsp_2(X6,X3,X0)
      | ~ m1_connsp_2(X5,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(X2,X1,X3)))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f145,f62])).

fof(f62,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK8(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK8(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v3_pre_topc(sK8(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v3_pre_topc(sK8(X3,X2,X1,X0,X5,X6),k1_tsep_1(X3,X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(X3,X2,X1)))
      | ~ m1_pre_topc(X1,X3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X4,sK8(X3,X2,X1,X0,X5,X6))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)))
      | m1_connsp_2(sK8(X3,X2,X1,X0,X5,X6),k1_tsep_1(X3,X2,X1),X4)
      | ~ m1_connsp_2(X5,X2,X0)
      | ~ m1_connsp_2(X6,X1,X0)
      | v2_struct_0(k1_tsep_1(X3,X2,X1))
      | ~ m1_pre_topc(k1_tsep_1(X3,X2,X1),X7)
      | ~ l1_pre_topc(X7) ) ),
    inference(resolution,[],[f144,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f144,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(k1_tsep_1(X4,X1,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X4,X1,X3)))
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X4)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X5,sK8(X4,X1,X3,X2,X0,X6))
      | ~ v3_pre_topc(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X4,X1,X3)))
      | m1_connsp_2(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3),X5)
      | ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_connsp_2(X6,X3,X2)
      | v2_struct_0(k1_tsep_1(X4,X1,X3)) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X4,X1,X3)))
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X4)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X5,sK8(X4,X1,X3,X2,X0,X6))
      | ~ v3_pre_topc(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X4,X1,X3)))
      | m1_connsp_2(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3),X5)
      | ~ l1_pre_topc(k1_tsep_1(X4,X1,X3))
      | ~ m1_connsp_2(X6,X3,X2)
      | v2_struct_0(k1_tsep_1(X4,X1,X3))
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X4)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f142,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f142,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(k1_tsep_1(X5,X4,X1))
      | ~ m1_connsp_2(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X4))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r2_hidden(X6,sK8(X5,X4,X1,X2,X3,X0))
      | ~ v3_pre_topc(sK8(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1))
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | m1_connsp_2(sK8(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6)
      | ~ l1_pre_topc(k1_tsep_1(X5,X4,X1))
      | ~ m1_connsp_2(X0,X1,X2)
      | v2_struct_0(k1_tsep_1(X5,X4,X1)) ) ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f64,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f140,plain,
    ( spl9_18
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f136,f86,f78,f138])).

fof(f78,plain,
    ( spl9_4
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f86,plain,
    ( spl9_6
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f136,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(superposition,[],[f87,f79])).

fof(f79,plain,
    ( sK3 = sK4
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f87,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f135,plain,
    ( spl9_17
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f131,f82,f74,f133])).

fof(f74,plain,
    ( spl9_3
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f82,plain,
    ( spl9_5
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f131,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f83,f75])).

fof(f75,plain,
    ( sK3 = sK5
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f83,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f130,plain,
    ( spl9_16
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f126,f74,f66,f128])).

fof(f66,plain,
    ( spl9_1
  <=> m1_connsp_2(sK7,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f126,plain,
    ( m1_connsp_2(sK7,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f67,f75])).

fof(f67,plain,
    ( m1_connsp_2(sK7,sK2,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f125,plain,
    ( spl9_15
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f121,f78,f70,f123])).

fof(f70,plain,
    ( spl9_2
  <=> m1_connsp_2(sK6,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f121,plain,
    ( m1_connsp_2(sK6,sK1,sK3)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f71,f79])).

fof(f71,plain,
    ( m1_connsp_2(sK6,sK1,sK4)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f120,plain,(
    ~ spl9_14 ),
    inference(avatar_split_clause,[],[f32,f118])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f33,f114])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f34,f110])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f35,f106])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f36,f102])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f39,f90])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f44,f70])).

fof(f44,plain,(
    m1_connsp_2(sK6,sK1,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f45,f66])).

fof(f45,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (14940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (14939)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (14934)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (14940)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f108,f112,f116,f120,f125,f130,f135,f140,f167,f171,f182,f184,f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl9_14 | spl9_11 | ~spl9_10 | spl9_9 | ~spl9_8 | ~spl9_12 | ~spl9_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f186,f150,f110,f94,f98,f102,f106,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl9_14 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl9_11 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl9_10 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl9_9 <=> v2_struct_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl9_8 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl9_12 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl9_19 <=> ! [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X3) | ~l1_pre_topc(X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~spl9_19),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_19),
% 0.21/0.50    inference(resolution,[],[f151,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X3) | ~l1_pre_topc(X3)) ) | ~spl9_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl9_14 | ~spl9_13 | ~spl9_12 | spl9_11 | ~spl9_10 | spl9_9 | ~spl9_8 | ~spl9_7 | ~spl9_18 | ~spl9_17 | ~spl9_15 | ~spl9_16 | spl9_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f183,f180,f128,f123,f133,f138,f90,f94,f98,f102,f106,f110,f114,f118])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl9_13 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl9_7 <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl9_18 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl9_17 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl9_15 <=> m1_connsp_2(sK6,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl9_16 <=> m1_connsp_2(sK7,sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl9_22 <=> r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ~m1_connsp_2(sK7,sK2,sK3) | ~m1_connsp_2(sK6,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_22),
% 0.21/0.50    inference(resolution,[],[f181,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X6,X2,X0,X7,X5,X1] : (r2_hidden(X5,sK8(X0,X1,X2,X5,X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X1] : (r2_hidden(X5,sK8(X0,X1,X2,X5,X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X3,sK8(X0,X1,X2,X3,X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tarski(sK8(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7)) & r2_hidden(X3,sK8(X0,X1,X2,X3,X6,X7)) & v3_pre_topc(sK8(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X7,X6,X3,X2,X1,X0] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) => (r1_tarski(sK8(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7)) & r2_hidden(X3,sK8(X0,X1,X2,X3,X6,X7)) & v3_pre_topc(sK8(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : (! [X7] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | (X3 != X5 | X3 != X4)) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tmap_1)).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7)) | spl9_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~spl9_16 | spl9_14 | ~spl9_13 | ~spl9_12 | spl9_11 | ~spl9_10 | spl9_9 | ~spl9_8 | ~spl9_18 | ~spl9_17 | ~spl9_15 | ~spl9_7 | ~spl9_22 | ~spl9_15 | ~spl9_16 | ~spl9_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f175,f157,f128,f123,f180,f90,f123,f133,f138,f94,f98,f102,f106,f110,f114,f118,f128])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl9_21 <=> ! [X1,X0,X2] : (~r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,X2)) | ~m1_connsp_2(X2,sK2,sK3) | ~m1_connsp_2(X1,sK1,sK3) | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,X2),k1_tsep_1(sK0,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_connsp_2(sK6,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_connsp_2(sK7,sK2,sK3) | (~spl9_15 | ~spl9_16 | ~spl9_21)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK6,sK7)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_connsp_2(sK6,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_connsp_2(sK7,sK2,sK3) | (~spl9_15 | ~spl9_16 | ~spl9_21)),
% 0.21/0.51    inference(resolution,[],[f173,f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(sK8(X3,X2,X0,X1,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),sK3) | ~m1_connsp_2(sK6,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(k1_tsep_1(X3,X2,X0))) | ~m1_pre_topc(X0,X3) | v2_struct_0(X0) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_connsp_2(sK7,X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f58,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X8] : (~r1_tarski(X8,k2_xboole_0(sK6,sK7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    (((((((! [X8] : (~r1_tarski(X8,k2_xboole_0(sK6,sK7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(sK7,sK2,sK5)) & m1_connsp_2(sK6,sK1,sK4)) & sK3 = sK5 & sK3 = sK4 & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f28,f27,f26,f25,f24,f23,f22,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,sK1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,sK1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),X3)) & m1_connsp_2(X7,sK2,X5)) & m1_connsp_2(X6,sK1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),X3)) & m1_connsp_2(X7,sK2,X5)) & m1_connsp_2(X6,sK1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,X5)) & m1_connsp_2(X6,sK1,X4)) & sK3 = X5 & sK3 = X4 & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,X5)) & m1_connsp_2(X6,sK1,X4)) & sK3 = X5 & sK3 = X4 & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,X5)) & m1_connsp_2(X6,sK1,sK4)) & sK3 = X5 & sK3 = sK4 & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,X5)) & m1_connsp_2(X6,sK1,sK4)) & sK3 = X5 & sK3 = sK4 & m1_subset_1(X5,u1_struct_0(sK2))) => (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,sK5)) & m1_connsp_2(X6,sK1,sK4)) & sK3 = sK5 & sK3 = sK4 & m1_subset_1(sK5,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,sK5)) & m1_connsp_2(X6,sK1,sK4)) => (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,sK5)) & m1_connsp_2(sK6,sK1,sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(X7,sK2,sK5)) => (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK6,sK7)) | ~m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)) & m1_connsp_2(sK7,sK2,sK5))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & (X3 = X5 & X3 = X4)) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tmap_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X6,X2,X0,X7,X5,X1] : (r1_tarski(sK8(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X1] : (r1_tarski(sK8(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tarski(sK8(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X0] : (m1_connsp_2(sK8(sK0,sK1,sK2,sK3,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),X0) | ~r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,sK6,sK7)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) | (~spl9_15 | ~spl9_16 | ~spl9_21)),
% 0.21/0.51    inference(resolution,[],[f172,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    m1_connsp_2(sK6,sK1,sK3) | ~spl9_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f123])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_connsp_2(X1,sK1,sK3) | ~r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,sK7)) | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,sK7),k1_tsep_1(sK0,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) | (~spl9_16 | ~spl9_21)),
% 0.21/0.51    inference(resolution,[],[f158,f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    m1_connsp_2(sK7,sK2,sK3) | ~spl9_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f128])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,sK2,sK3) | ~r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,X2)) | ~m1_connsp_2(X1,sK1,sK3) | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,X2),k1_tsep_1(sK0,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) | ~spl9_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl9_14 | ~spl9_12 | spl9_11 | ~spl9_10 | spl9_9 | ~spl9_8 | ~spl9_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f169,f153,f94,f98,f102,f106,f110,f118])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl9_20 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_20),
% 0.21/0.51    inference(resolution,[],[f154,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl9_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl9_19 | spl9_20 | ~spl9_17 | spl9_21 | spl9_14 | ~spl9_13 | ~spl9_12 | spl9_11 | ~spl9_10 | spl9_9 | ~spl9_8 | ~spl9_18 | ~spl9_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f148,f90,f138,f94,f98,f102,f106,f110,f114,f118,f157,f133,f153,f150])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,sK8(sK0,sK1,sK2,sK3,X1,X2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | m1_connsp_2(sK8(sK0,sK1,sK2,sK3,X1,X2),k1_tsep_1(sK0,sK1,sK2),X0) | ~m1_connsp_2(X1,sK1,sK3) | ~m1_connsp_2(X2,sK2,sK3) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X3) | ~l1_pre_topc(X3)) ) | ~spl9_7),
% 0.21/0.51    inference(resolution,[],[f147,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl9_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(X0,u1_struct_0(k1_tsep_1(X2,X1,X3))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r2_hidden(X4,sK8(X2,X1,X3,X0,X5,X6)) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X1,X3))) | m1_connsp_2(sK8(X2,X1,X3,X0,X5,X6),k1_tsep_1(X2,X1,X3),X4) | ~m1_connsp_2(X5,X1,X0) | ~m1_connsp_2(X6,X3,X0) | v2_struct_0(k1_tsep_1(X2,X1,X3)) | ~m1_pre_topc(k1_tsep_1(X2,X1,X3),X7) | ~l1_pre_topc(X7)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(X2,X1,X3))) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r2_hidden(X4,sK8(X2,X1,X3,X0,X5,X6)) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X1,X3))) | m1_connsp_2(sK8(X2,X1,X3,X0,X5,X6),k1_tsep_1(X2,X1,X3),X4) | ~m1_connsp_2(X5,X1,X0) | ~m1_connsp_2(X6,X3,X0) | v2_struct_0(k1_tsep_1(X2,X1,X3)) | ~m1_pre_topc(k1_tsep_1(X2,X1,X3),X7) | ~l1_pre_topc(X7) | ~m1_connsp_2(X6,X3,X0) | ~m1_connsp_2(X5,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(X2,X1,X3))) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f145,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X6,X2,X0,X7,X5,X1] : (v3_pre_topc(sK8(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X1] : (v3_pre_topc(sK8(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v3_pre_topc(sK8(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v3_pre_topc(sK8(X3,X2,X1,X0,X5,X6),k1_tsep_1(X3,X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(X3,X2,X1))) | ~m1_pre_topc(X1,X3) | v2_struct_0(X1) | ~m1_pre_topc(X2,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r2_hidden(X4,sK8(X3,X2,X1,X0,X5,X6)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X3,X2,X1))) | m1_connsp_2(sK8(X3,X2,X1,X0,X5,X6),k1_tsep_1(X3,X2,X1),X4) | ~m1_connsp_2(X5,X2,X0) | ~m1_connsp_2(X6,X1,X0) | v2_struct_0(k1_tsep_1(X3,X2,X1)) | ~m1_pre_topc(k1_tsep_1(X3,X2,X1),X7) | ~l1_pre_topc(X7)) )),
% 0.21/0.51    inference(resolution,[],[f144,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~l1_pre_topc(k1_tsep_1(X4,X1,X3)) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tsep_1(X4,X1,X3))) | ~m1_pre_topc(X3,X4) | v2_struct_0(X3) | ~m1_pre_topc(X1,X4) | v2_struct_0(X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r2_hidden(X5,sK8(X4,X1,X3,X2,X0,X6)) | ~v3_pre_topc(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X4,X1,X3))) | m1_connsp_2(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3),X5) | ~m1_connsp_2(X0,X1,X2) | ~m1_connsp_2(X6,X3,X2) | v2_struct_0(k1_tsep_1(X4,X1,X3))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tsep_1(X4,X1,X3))) | ~m1_pre_topc(X3,X4) | v2_struct_0(X3) | ~m1_pre_topc(X1,X4) | v2_struct_0(X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~r2_hidden(X5,sK8(X4,X1,X3,X2,X0,X6)) | ~v3_pre_topc(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X4,X1,X3))) | m1_connsp_2(sK8(X4,X1,X3,X2,X0,X6),k1_tsep_1(X4,X1,X3),X5) | ~l1_pre_topc(k1_tsep_1(X4,X1,X3)) | ~m1_connsp_2(X6,X3,X2) | v2_struct_0(k1_tsep_1(X4,X1,X3)) | ~m1_pre_topc(X3,X4) | v2_struct_0(X3) | ~m1_pre_topc(X1,X4) | v2_struct_0(X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.51    inference(resolution,[],[f142,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(k1_tsep_1(X5,X4,X1)) | ~m1_connsp_2(X3,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X4)) | ~m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1))) | ~m1_pre_topc(X1,X5) | v2_struct_0(X1) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~r2_hidden(X6,sK8(X5,X4,X1,X2,X3,X0)) | ~v3_pre_topc(sK8(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1)) | ~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1))) | m1_connsp_2(sK8(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6) | ~l1_pre_topc(k1_tsep_1(X5,X4,X1)) | ~m1_connsp_2(X0,X1,X2) | v2_struct_0(k1_tsep_1(X5,X4,X1))) )),
% 0.21/0.51    inference(resolution,[],[f64,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X6,X2,X0,X7,X5,X1] : (m1_subset_1(sK8(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X1] : (m1_subset_1(sK8(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl9_18 | ~spl9_4 | ~spl9_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f86,f78,f138])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl9_4 <=> sK3 = sK4),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl9_6 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK1)) | (~spl9_4 | ~spl9_6)),
% 0.21/0.51    inference(superposition,[],[f87,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    sK3 = sK4 | ~spl9_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl9_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl9_17 | ~spl9_3 | ~spl9_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f131,f82,f74,f133])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl9_3 <=> sK3 = sK5),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl9_5 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl9_3 | ~spl9_5)),
% 0.21/0.51    inference(superposition,[],[f83,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    sK3 = sK5 | ~spl9_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl9_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl9_16 | ~spl9_1 | ~spl9_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f126,f74,f66,f128])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl9_1 <=> m1_connsp_2(sK7,sK2,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    m1_connsp_2(sK7,sK2,sK3) | (~spl9_1 | ~spl9_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f67,f75])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    m1_connsp_2(sK7,sK2,sK5) | ~spl9_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl9_15 | ~spl9_2 | ~spl9_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f121,f78,f70,f123])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl9_2 <=> m1_connsp_2(sK6,sK1,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    m1_connsp_2(sK6,sK1,sK3) | (~spl9_2 | ~spl9_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f71,f79])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    m1_connsp_2(sK6,sK1,sK4) | ~spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~spl9_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f118])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl9_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f114])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl9_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f110])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~spl9_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f106])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl9_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f102])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~spl9_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f98])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl9_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f94])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl9_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f90])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl9_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl9_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f82])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl9_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f78])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    sK3 = sK4),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl9_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f74])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    sK3 = sK5),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f70])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_connsp_2(sK6,sK1,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl9_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f66])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    m1_connsp_2(sK7,sK2,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (14940)------------------------------
% 0.21/0.51  % (14940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14940)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (14940)Memory used [KB]: 10874
% 0.21/0.51  % (14940)Time elapsed: 0.077 s
% 0.21/0.51  % (14940)------------------------------
% 0.21/0.51  % (14940)------------------------------
% 0.21/0.51  % (14933)Success in time 0.151 s
%------------------------------------------------------------------------------
