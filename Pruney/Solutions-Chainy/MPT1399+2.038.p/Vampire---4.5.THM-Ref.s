%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:17 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 196 expanded)
%              Number of leaves         :   28 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  387 (1298 expanded)
%              Number of equality atoms :   24 (  99 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f70,f75,f80,f85,f90,f107,f117,f133,f142,f148,f154,f169,f172])).

fof(f172,plain,
    ( ~ spl4_17
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f171,f151,f145,f113,f87,f57,f166])).

fof(f166,plain,
    ( spl4_17
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f57,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f113,plain,
    ( spl4_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f145,plain,
    ( spl4_14
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f151,plain,
    ( spl4_15
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f171,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f147,f108,f91,f153,f119])).

fof(f119,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f96,f115])).

fof(f115,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f96,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f43,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f43,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f153,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f108,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f147,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f169,plain,
    ( spl4_17
    | ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f156,f139,f130,f166])).

fof(f130,plain,
    ( spl4_12
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( spl4_13
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f156,plain,
    ( r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl4_12
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f132,f141,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (22947)Refutation not found, incomplete strategy% (22947)------------------------------
% (22947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22947)Termination reason: Refutation not found, incomplete strategy

% (22947)Memory used [KB]: 1663
% (22947)Time elapsed: 0.054 s
% (22947)------------------------------
% (22947)------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f141,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f132,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f154,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f149,f77,f72,f151])).

fof(f72,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f77,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f149,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f79,f74,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f148,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f143,f77,f72,f145])).

fof(f143,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f79,f74,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f142,plain,
    ( ~ spl4_13
    | spl4_6
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f137,f113,f104,f82,f139])).

fof(f82,plain,
    ( spl4_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f104,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f137,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_6
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f135,f115])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_6
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f84,f106,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f84,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f133,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f123,f113,f67,f130])).

fof(f67,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f123,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f69,f115])).

fof(f69,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f117,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f111,f104,f113])).

fof(f111,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f45,f106])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f102,f72,f104])).

fof(f102,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f74,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f90,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f44,f57])).

fof(f44,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (823820288)
% 0.22/0.38  ipcrm: permission denied for id (823918598)
% 0.22/0.38  ipcrm: permission denied for id (823951369)
% 0.22/0.38  ipcrm: permission denied for id (823984138)
% 0.22/0.39  ipcrm: permission denied for id (824049676)
% 0.22/0.39  ipcrm: permission denied for id (824082448)
% 0.22/0.41  ipcrm: permission denied for id (824180771)
% 0.22/0.42  ipcrm: permission denied for id (824344618)
% 0.22/0.43  ipcrm: permission denied for id (824377389)
% 0.22/0.43  ipcrm: permission denied for id (824508465)
% 0.22/0.44  ipcrm: permission denied for id (824574009)
% 0.22/0.45  ipcrm: permission denied for id (824672320)
% 0.22/0.46  ipcrm: permission denied for id (824737859)
% 0.22/0.46  ipcrm: permission denied for id (824836166)
% 0.22/0.47  ipcrm: permission denied for id (824868938)
% 0.22/0.47  ipcrm: permission denied for id (824901709)
% 0.22/0.49  ipcrm: permission denied for id (825032790)
% 0.22/0.49  ipcrm: permission denied for id (825065561)
% 0.22/0.51  ipcrm: permission denied for id (825229413)
% 0.22/0.52  ipcrm: permission denied for id (825360491)
% 0.22/0.52  ipcrm: permission denied for id (825393260)
% 0.22/0.52  ipcrm: permission denied for id (825426030)
% 0.22/0.53  ipcrm: permission denied for id (825458801)
% 0.22/0.54  ipcrm: permission denied for id (825524344)
% 0.22/0.54  ipcrm: permission denied for id (825589882)
% 0.40/0.66  % (22926)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.40/0.66  % (22930)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.40/0.67  % (22932)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.40/0.67  % (22932)Refutation found. Thanks to Tanya!
% 0.40/0.67  % SZS status Theorem for theBenchmark
% 0.40/0.67  % (22948)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.40/0.67  % (22931)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.40/0.67  % (22949)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.40/0.68  % (22943)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.40/0.68  % (22947)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.40/0.68  % (22939)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.40/0.68  % (22933)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.40/0.68  % (22942)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.40/0.68  % (22935)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.40/0.68  % (22940)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.40/0.68  % SZS output start Proof for theBenchmark
% 0.40/0.68  fof(f173,plain,(
% 0.40/0.68    $false),
% 0.40/0.68    inference(avatar_sat_refutation,[],[f60,f70,f75,f80,f85,f90,f107,f117,f133,f142,f148,f154,f169,f172])).
% 0.40/0.68  fof(f172,plain,(
% 0.40/0.68    ~spl4_17 | ~spl4_1 | ~spl4_7 | ~spl4_10 | ~spl4_14 | ~spl4_15),
% 0.40/0.68    inference(avatar_split_clause,[],[f171,f151,f145,f113,f87,f57,f166])).
% 0.40/0.68  fof(f166,plain,(
% 0.40/0.68    spl4_17 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.40/0.68  fof(f57,plain,(
% 0.40/0.68    spl4_1 <=> k1_xboole_0 = sK2),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.40/0.68  fof(f87,plain,(
% 0.40/0.68    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.40/0.68  fof(f113,plain,(
% 0.40/0.68    spl4_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.40/0.68  fof(f145,plain,(
% 0.40/0.68    spl4_14 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.40/0.68  fof(f151,plain,(
% 0.40/0.68    spl4_15 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.40/0.68  fof(f171,plain,(
% 0.40/0.68    ~r2_hidden(sK1,k2_struct_0(sK0)) | (~spl4_1 | ~spl4_7 | ~spl4_10 | ~spl4_14 | ~spl4_15)),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f147,f108,f91,f153,f119])).
% 0.40/0.68  fof(f119,plain,(
% 0.40/0.68    ( ! [X3] : (~r2_hidden(sK1,X3) | r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | (~spl4_1 | ~spl4_10)),
% 0.40/0.68    inference(backward_demodulation,[],[f96,f115])).
% 0.40/0.68  fof(f115,plain,(
% 0.40/0.68    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_10),
% 0.40/0.68    inference(avatar_component_clause,[],[f113])).
% 0.40/0.68  fof(f96,plain,(
% 0.40/0.68    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_1),
% 0.40/0.68    inference(backward_demodulation,[],[f43,f59])).
% 0.40/0.68  fof(f59,plain,(
% 0.40/0.68    k1_xboole_0 = sK2 | ~spl4_1),
% 0.40/0.68    inference(avatar_component_clause,[],[f57])).
% 0.40/0.68  fof(f43,plain,(
% 0.40/0.68    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.40/0.68    inference(cnf_transformation,[],[f30])).
% 0.40/0.68  fof(f30,plain,(
% 0.40/0.68    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.40/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 0.40/0.68  fof(f27,plain,(
% 0.40/0.68    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.40/0.68    introduced(choice_axiom,[])).
% 0.40/0.68  fof(f28,plain,(
% 0.40/0.68    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.40/0.68    introduced(choice_axiom,[])).
% 0.40/0.68  fof(f29,plain,(
% 0.40/0.68    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.40/0.68    introduced(choice_axiom,[])).
% 0.40/0.68  fof(f26,plain,(
% 0.40/0.68    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.40/0.68    inference(flattening,[],[f25])).
% 0.40/0.68  fof(f25,plain,(
% 0.40/0.68    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.40/0.68    inference(nnf_transformation,[],[f14])).
% 0.40/0.68  fof(f14,plain,(
% 0.40/0.68    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.40/0.68    inference(flattening,[],[f13])).
% 0.40/0.68  fof(f13,plain,(
% 0.40/0.68    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.40/0.68    inference(ennf_transformation,[],[f12])).
% 0.40/0.68  fof(f12,negated_conjecture,(
% 0.40/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.40/0.68    inference(negated_conjecture,[],[f11])).
% 0.40/0.68  fof(f11,conjecture,(
% 0.40/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.40/0.68  fof(f153,plain,(
% 0.40/0.68    v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl4_15),
% 0.40/0.68    inference(avatar_component_clause,[],[f151])).
% 0.40/0.68  fof(f91,plain,(
% 0.40/0.68    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.40/0.68    inference(forward_demodulation,[],[f53,f46])).
% 0.40/0.68  fof(f46,plain,(
% 0.40/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.40/0.68    inference(cnf_transformation,[],[f3])).
% 0.40/0.68  fof(f3,axiom,(
% 0.40/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.40/0.68  fof(f53,plain,(
% 0.40/0.68    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.40/0.68    inference(cnf_transformation,[],[f4])).
% 0.40/0.68  fof(f4,axiom,(
% 0.40/0.68    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.40/0.68  fof(f108,plain,(
% 0.40/0.68    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_7),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f89,f51])).
% 0.40/0.68  fof(f51,plain,(
% 0.40/0.68    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f34])).
% 0.40/0.68  fof(f34,plain,(
% 0.40/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.40/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.40/0.68  fof(f33,plain,(
% 0.40/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.40/0.68    introduced(choice_axiom,[])).
% 0.40/0.68  fof(f32,plain,(
% 0.40/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.40/0.68    inference(rectify,[],[f31])).
% 0.40/0.68  fof(f31,plain,(
% 0.40/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.40/0.68    inference(nnf_transformation,[],[f1])).
% 0.40/0.68  fof(f1,axiom,(
% 0.40/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.40/0.68  fof(f89,plain,(
% 0.40/0.68    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 0.40/0.68    inference(avatar_component_clause,[],[f87])).
% 0.40/0.68  fof(f147,plain,(
% 0.40/0.68    v4_pre_topc(k2_struct_0(sK0),sK0) | ~spl4_14),
% 0.40/0.68    inference(avatar_component_clause,[],[f145])).
% 0.40/0.68  fof(f169,plain,(
% 0.40/0.68    spl4_17 | ~spl4_12 | spl4_13),
% 0.40/0.68    inference(avatar_split_clause,[],[f156,f139,f130,f166])).
% 0.40/0.68  fof(f130,plain,(
% 0.40/0.68    spl4_12 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.40/0.68  fof(f139,plain,(
% 0.40/0.68    spl4_13 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.40/0.68  fof(f156,plain,(
% 0.40/0.68    r2_hidden(sK1,k2_struct_0(sK0)) | (~spl4_12 | spl4_13)),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f132,f141,f50])).
% 0.40/0.68  fof(f50,plain,(
% 0.40/0.68    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f21])).
% 0.40/0.68  fof(f21,plain,(
% 0.40/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.40/0.68    inference(flattening,[],[f20])).
% 0.40/0.68  fof(f20,plain,(
% 0.40/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.40/0.68    inference(ennf_transformation,[],[f5])).
% 0.40/0.68  % (22947)Refutation not found, incomplete strategy% (22947)------------------------------
% 0.40/0.68  % (22947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.68  % (22947)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.68  
% 0.40/0.68  % (22947)Memory used [KB]: 1663
% 0.40/0.68  % (22947)Time elapsed: 0.054 s
% 0.40/0.68  % (22947)------------------------------
% 0.40/0.68  % (22947)------------------------------
% 0.40/0.68  fof(f5,axiom,(
% 0.40/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.40/0.68  fof(f141,plain,(
% 0.40/0.68    ~v1_xboole_0(k2_struct_0(sK0)) | spl4_13),
% 0.40/0.68    inference(avatar_component_clause,[],[f139])).
% 0.40/0.68  fof(f132,plain,(
% 0.40/0.68    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl4_12),
% 0.40/0.68    inference(avatar_component_clause,[],[f130])).
% 0.40/0.68  fof(f154,plain,(
% 0.40/0.68    spl4_15 | ~spl4_4 | ~spl4_5),
% 0.40/0.68    inference(avatar_split_clause,[],[f149,f77,f72,f151])).
% 0.40/0.68  fof(f72,plain,(
% 0.40/0.68    spl4_4 <=> l1_pre_topc(sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.40/0.68  fof(f77,plain,(
% 0.40/0.68    spl4_5 <=> v2_pre_topc(sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.40/0.68  fof(f149,plain,(
% 0.40/0.68    v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl4_4 | ~spl4_5)),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f79,f74,f49])).
% 0.40/0.68  fof(f49,plain,(
% 0.40/0.68    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f19])).
% 0.40/0.68  fof(f19,plain,(
% 0.40/0.68    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.40/0.68    inference(flattening,[],[f18])).
% 0.40/0.68  fof(f18,plain,(
% 0.40/0.68    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.40/0.68    inference(ennf_transformation,[],[f10])).
% 0.40/0.68  fof(f10,axiom,(
% 0.40/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.40/0.68  fof(f74,plain,(
% 0.40/0.68    l1_pre_topc(sK0) | ~spl4_4),
% 0.40/0.68    inference(avatar_component_clause,[],[f72])).
% 0.40/0.68  fof(f79,plain,(
% 0.40/0.68    v2_pre_topc(sK0) | ~spl4_5),
% 0.40/0.68    inference(avatar_component_clause,[],[f77])).
% 0.40/0.68  fof(f148,plain,(
% 0.40/0.68    spl4_14 | ~spl4_4 | ~spl4_5),
% 0.40/0.68    inference(avatar_split_clause,[],[f143,f77,f72,f145])).
% 0.40/0.68  fof(f143,plain,(
% 0.40/0.68    v4_pre_topc(k2_struct_0(sK0),sK0) | (~spl4_4 | ~spl4_5)),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f79,f74,f48])).
% 0.40/0.68  fof(f48,plain,(
% 0.40/0.68    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f17])).
% 0.40/0.68  fof(f17,plain,(
% 0.40/0.68    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.40/0.68    inference(flattening,[],[f16])).
% 0.40/0.68  fof(f16,plain,(
% 0.40/0.68    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.40/0.68    inference(ennf_transformation,[],[f9])).
% 0.40/0.68  fof(f9,axiom,(
% 0.40/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.40/0.68  fof(f142,plain,(
% 0.40/0.68    ~spl4_13 | spl4_6 | ~spl4_9 | ~spl4_10),
% 0.40/0.68    inference(avatar_split_clause,[],[f137,f113,f104,f82,f139])).
% 0.40/0.68  fof(f82,plain,(
% 0.40/0.68    spl4_6 <=> v2_struct_0(sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.40/0.68  fof(f104,plain,(
% 0.40/0.68    spl4_9 <=> l1_struct_0(sK0)),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.40/0.68  fof(f137,plain,(
% 0.40/0.68    ~v1_xboole_0(k2_struct_0(sK0)) | (spl4_6 | ~spl4_9 | ~spl4_10)),
% 0.40/0.68    inference(forward_demodulation,[],[f135,f115])).
% 0.40/0.68  fof(f135,plain,(
% 0.40/0.68    ~v1_xboole_0(u1_struct_0(sK0)) | (spl4_6 | ~spl4_9)),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f84,f106,f54])).
% 0.40/0.68  fof(f54,plain,(
% 0.40/0.68    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f23])).
% 0.40/0.68  fof(f23,plain,(
% 0.40/0.68    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.40/0.68    inference(flattening,[],[f22])).
% 0.40/0.68  fof(f22,plain,(
% 0.40/0.68    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.40/0.68    inference(ennf_transformation,[],[f8])).
% 0.40/0.68  fof(f8,axiom,(
% 0.40/0.68    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.40/0.68  fof(f106,plain,(
% 0.40/0.68    l1_struct_0(sK0) | ~spl4_9),
% 0.40/0.68    inference(avatar_component_clause,[],[f104])).
% 0.40/0.68  fof(f84,plain,(
% 0.40/0.68    ~v2_struct_0(sK0) | spl4_6),
% 0.40/0.68    inference(avatar_component_clause,[],[f82])).
% 0.40/0.68  fof(f133,plain,(
% 0.40/0.68    spl4_12 | ~spl4_3 | ~spl4_10),
% 0.40/0.68    inference(avatar_split_clause,[],[f123,f113,f67,f130])).
% 0.40/0.68  fof(f67,plain,(
% 0.40/0.68    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.40/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.40/0.68  fof(f123,plain,(
% 0.40/0.68    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl4_3 | ~spl4_10)),
% 0.40/0.68    inference(backward_demodulation,[],[f69,f115])).
% 0.40/0.68  fof(f69,plain,(
% 0.40/0.68    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 0.40/0.68    inference(avatar_component_clause,[],[f67])).
% 0.40/0.68  fof(f117,plain,(
% 0.40/0.68    spl4_10 | ~spl4_9),
% 0.40/0.68    inference(avatar_split_clause,[],[f111,f104,f113])).
% 0.40/0.68  fof(f111,plain,(
% 0.40/0.68    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.40/0.68    inference(resolution,[],[f45,f106])).
% 0.40/0.68  fof(f45,plain,(
% 0.40/0.68    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f15])).
% 0.40/0.68  fof(f15,plain,(
% 0.40/0.68    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.40/0.68    inference(ennf_transformation,[],[f6])).
% 0.40/0.68  fof(f6,axiom,(
% 0.40/0.68    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.40/0.68  fof(f107,plain,(
% 0.40/0.68    spl4_9 | ~spl4_4),
% 0.40/0.68    inference(avatar_split_clause,[],[f102,f72,f104])).
% 0.40/0.68  fof(f102,plain,(
% 0.40/0.68    l1_struct_0(sK0) | ~spl4_4),
% 0.40/0.68    inference(unit_resulting_resolution,[],[f74,f55])).
% 0.40/0.68  fof(f55,plain,(
% 0.40/0.68    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.40/0.68    inference(cnf_transformation,[],[f24])).
% 0.40/0.68  fof(f24,plain,(
% 0.40/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.40/0.68    inference(ennf_transformation,[],[f7])).
% 0.40/0.68  fof(f7,axiom,(
% 0.40/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.40/0.68  fof(f90,plain,(
% 0.40/0.68    spl4_7),
% 0.40/0.68    inference(avatar_split_clause,[],[f47,f87])).
% 0.40/0.68  fof(f47,plain,(
% 0.40/0.68    v1_xboole_0(k1_xboole_0)),
% 0.40/0.68    inference(cnf_transformation,[],[f2])).
% 0.40/0.68  fof(f2,axiom,(
% 0.40/0.68    v1_xboole_0(k1_xboole_0)),
% 0.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.40/0.68  fof(f85,plain,(
% 0.40/0.68    ~spl4_6),
% 0.40/0.68    inference(avatar_split_clause,[],[f35,f82])).
% 0.40/0.68  fof(f35,plain,(
% 0.40/0.68    ~v2_struct_0(sK0)),
% 0.40/0.68    inference(cnf_transformation,[],[f30])).
% 0.40/0.68  fof(f80,plain,(
% 0.40/0.68    spl4_5),
% 0.40/0.68    inference(avatar_split_clause,[],[f36,f77])).
% 0.40/0.68  fof(f36,plain,(
% 0.40/0.68    v2_pre_topc(sK0)),
% 0.40/0.68    inference(cnf_transformation,[],[f30])).
% 0.40/0.68  fof(f75,plain,(
% 0.40/0.68    spl4_4),
% 0.40/0.68    inference(avatar_split_clause,[],[f37,f72])).
% 0.40/0.68  fof(f37,plain,(
% 0.40/0.68    l1_pre_topc(sK0)),
% 0.40/0.68    inference(cnf_transformation,[],[f30])).
% 0.40/0.68  fof(f70,plain,(
% 0.40/0.68    spl4_3),
% 0.40/0.68    inference(avatar_split_clause,[],[f38,f67])).
% 0.40/0.68  fof(f38,plain,(
% 0.40/0.68    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.40/0.68    inference(cnf_transformation,[],[f30])).
% 0.40/0.68  fof(f60,plain,(
% 0.40/0.68    spl4_1),
% 0.40/0.68    inference(avatar_split_clause,[],[f44,f57])).
% 0.40/0.68  fof(f44,plain,(
% 0.40/0.68    k1_xboole_0 = sK2),
% 0.40/0.68    inference(cnf_transformation,[],[f30])).
% 0.40/0.68  % SZS output end Proof for theBenchmark
% 0.40/0.68  % (22932)------------------------------
% 0.40/0.68  % (22932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.68  % (22932)Termination reason: Refutation
% 0.40/0.68  
% 0.40/0.68  % (22932)Memory used [KB]: 10746
% 0.40/0.68  % (22932)Time elapsed: 0.080 s
% 0.40/0.68  % (22932)------------------------------
% 0.40/0.68  % (22932)------------------------------
% 0.40/0.68  % (22934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.40/0.68  % (22765)Success in time 0.316 s
%------------------------------------------------------------------------------
