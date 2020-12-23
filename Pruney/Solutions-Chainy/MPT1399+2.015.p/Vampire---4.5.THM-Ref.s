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
% DateTime   : Thu Dec  3 13:15:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 370 expanded)
%              Number of leaves         :   33 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  471 (3217 expanded)
%              Number of equality atoms :   37 ( 281 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f141,f143,f146,f148,f159,f161,f166,f222,f244,f374,f443,f445,f489,f504])).

fof(f504,plain,(
    ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl3_35 ),
    inference(resolution,[],[f488,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f488,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl3_35
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f489,plain,
    ( spl3_35
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f469,f213,f136,f117,f486])).

fof(f117,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f136,plain,
    ( spl3_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f213,plain,
    ( spl3_16
  <=> u1_struct_0(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f469,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_16 ),
    inference(superposition,[],[f64,f215])).

fof(f215,plain,
    ( u1_struct_0(sK0) = sK2
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f445,plain,
    ( spl3_16
    | ~ spl3_17
    | spl3_12
    | spl3_20 ),
    inference(avatar_split_clause,[],[f419,f255,f163,f217,f213])).

fof(f217,plain,
    ( spl3_17
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f163,plain,
    ( spl3_12
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f255,plain,
    ( spl3_20
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f419,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK2
    | spl3_12
    | spl3_20 ),
    inference(resolution,[],[f283,f165])).

fof(f165,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f283,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | ~ m1_subset_1(sK1,X0)
        | sK2 = X0 )
    | spl3_20 ),
    inference(resolution,[],[f256,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | sK2 = X1 ) ),
    inference(resolution,[],[f114,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f51,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | sK2 = X0 ) ),
    inference(superposition,[],[f76,f73])).

fof(f73,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f69,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f63,f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f256,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f443,plain,(
    ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl3_20 ),
    inference(resolution,[],[f437,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f437,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f257,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f257,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f374,plain,
    ( spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f372,f136,f133])).

fof(f133,plain,
    ( spl3_9
  <=> ! [X0] :
        ( v4_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f372,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | v4_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f74,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f244,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f226,f72])).

fof(f226,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f96,f67])).

fof(f96,plain,
    ( r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_4
  <=> r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f222,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f219,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f219,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f217])).

fof(f166,plain,
    ( spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f111,f163,f102,f91,f95])).

fof(f91,plain,
    ( spl3_3
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( spl3_5
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f111,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | r2_hidden(u1_struct_0(sK0),sK2) ),
    inference(resolution,[],[f50,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f50,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f161,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | ~ spl3_9
    | spl3_11 ),
    inference(avatar_split_clause,[],[f160,f156,f133,f121,f125])).

fof(f125,plain,
    ( spl3_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f121,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f156,plain,
    ( spl3_11
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f160,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_9
    | spl3_11 ),
    inference(resolution,[],[f158,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( v4_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f158,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( ~ spl3_8
    | ~ spl3_11
    | spl3_3 ),
    inference(avatar_split_clause,[],[f154,f91,f156,f125])).

fof(f154,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(resolution,[],[f152,f92])).

fof(f92,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f152,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ v4_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f144,f74])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(sK2,X0)
      | v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f61,f73])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f148,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f129,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(resolution,[],[f119,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f119,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f146,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f127,f44])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f143,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f123,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f123,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f141,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f138,f71])).

fof(f71,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f138,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f128,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | spl3_5 ),
    inference(avatar_split_clause,[],[f115,f102,f125,f121,f117])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_struct_0(sK0)
    | spl3_5 ),
    inference(resolution,[],[f78,f103])).

fof(f103,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f78,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f65,f59])).

fof(f59,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f65,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:13:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.42  % (428)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.43  % (428)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f505,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f128,f141,f143,f146,f148,f159,f161,f166,f222,f244,f374,f443,f445,f489,f504])).
% 0.20/0.43  fof(f504,plain,(
% 0.20/0.43    ~spl3_35),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f503])).
% 0.20/0.43  fof(f503,plain,(
% 0.20/0.43    $false | ~spl3_35),
% 0.20/0.43    inference(resolution,[],[f488,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f17])).
% 0.20/0.43  fof(f17,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.20/0.43  fof(f488,plain,(
% 0.20/0.43    v2_struct_0(sK0) | ~spl3_35),
% 0.20/0.43    inference(avatar_component_clause,[],[f486])).
% 0.20/0.43  fof(f486,plain,(
% 0.20/0.43    spl3_35 <=> v2_struct_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.43  fof(f489,plain,(
% 0.20/0.43    spl3_35 | ~spl3_6 | ~spl3_10 | ~spl3_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f469,f213,f136,f117,f486])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    spl3_6 <=> l1_struct_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    spl3_10 <=> v1_xboole_0(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.43  fof(f213,plain,(
% 0.20/0.43    spl3_16 <=> u1_struct_0(sK0) = sK2),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.43  fof(f469,plain,(
% 0.20/0.43    ~v1_xboole_0(sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_16),
% 0.20/0.43    inference(superposition,[],[f64,f215])).
% 0.20/0.43  fof(f215,plain,(
% 0.20/0.43    u1_struct_0(sK0) = sK2 | ~spl3_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f213])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.43  fof(f445,plain,(
% 0.20/0.43    spl3_16 | ~spl3_17 | spl3_12 | spl3_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f419,f255,f163,f217,f213])).
% 0.20/0.43  fof(f217,plain,(
% 0.20/0.43    spl3_17 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.43  fof(f163,plain,(
% 0.20/0.43    spl3_12 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f255,plain,(
% 0.20/0.43    spl3_20 <=> r2_hidden(sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.43  fof(f419,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = sK2 | (spl3_12 | spl3_20)),
% 0.20/0.43    inference(resolution,[],[f283,f165])).
% 0.20/0.43  fof(f165,plain,(
% 0.20/0.43    ~r2_hidden(sK1,u1_struct_0(sK0)) | spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f163])).
% 0.20/0.43  fof(f283,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK1,X0) | ~m1_subset_1(sK1,X0) | sK2 = X0) ) | spl3_20),
% 0.20/0.43    inference(resolution,[],[f256,f167])).
% 0.20/0.43  fof(f167,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK2 = X1) )),
% 0.20/0.43    inference(resolution,[],[f114,f74])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f56,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    k1_xboole_0 = sK2),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r2_hidden(X1,sK2) | ~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | sK2 = X0) )),
% 0.20/0.43    inference(superposition,[],[f76,f73])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f55,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f58,f69])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.20/0.43    inference(definition_unfolding,[],[f54,f51])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK2 = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f63,f51])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(flattening,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 0.20/0.43  fof(f256,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK2) | spl3_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f255])).
% 0.20/0.43  fof(f443,plain,(
% 0.20/0.43    ~spl3_20),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f442])).
% 0.20/0.43  fof(f442,plain,(
% 0.20/0.43    $false | ~spl3_20),
% 0.20/0.43    inference(resolution,[],[f437,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f53,f51])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.43  fof(f437,plain,(
% 0.20/0.43    ~r1_tarski(sK2,sK1) | ~spl3_20),
% 0.20/0.43    inference(resolution,[],[f257,f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.43  fof(f257,plain,(
% 0.20/0.43    r2_hidden(sK1,sK2) | ~spl3_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f255])).
% 0.20/0.43  fof(f374,plain,(
% 0.20/0.43    spl3_9 | ~spl3_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f372,f136,f133])).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    spl3_9 <=> ! [X0] : (v4_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f372,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(sK2) | v4_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.43    inference(resolution,[],[f74,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.43  fof(f244,plain,(
% 0.20/0.43    ~spl3_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f243])).
% 0.20/0.43  fof(f243,plain,(
% 0.20/0.43    $false | ~spl3_4),
% 0.20/0.43    inference(resolution,[],[f226,f72])).
% 0.20/0.43  fof(f226,plain,(
% 0.20/0.43    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_4),
% 0.20/0.43    inference(resolution,[],[f96,f67])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    r2_hidden(u1_struct_0(sK0),sK2) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f95])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    spl3_4 <=> r2_hidden(u1_struct_0(sK0),sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f222,plain,(
% 0.20/0.43    spl3_17),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f221])).
% 0.20/0.43  fof(f221,plain,(
% 0.20/0.43    $false | spl3_17),
% 0.20/0.43    inference(resolution,[],[f219,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f217])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    spl3_4 | ~spl3_3 | ~spl3_5 | ~spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f111,f163,f102,f91,f95])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl3_3 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl3_5 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | r2_hidden(u1_struct_0(sK0),sK2)),
% 0.20/0.43    inference(resolution,[],[f50,f77])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f75,f73])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f57,f70])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | r2_hidden(X3,sK2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    ~spl3_8 | ~spl3_7 | ~spl3_9 | spl3_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f160,f156,f133,f121,f125])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    spl3_8 <=> l1_pre_topc(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    spl3_7 <=> v2_pre_topc(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    spl3_11 <=> v4_pre_topc(sK2,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.43  fof(f160,plain,(
% 0.20/0.43    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl3_9 | spl3_11)),
% 0.20/0.43    inference(resolution,[],[f158,f134])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    ( ! [X0] : (v4_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f133])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    ~v4_pre_topc(sK2,sK0) | spl3_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f156])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    ~spl3_8 | ~spl3_11 | spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f154,f91,f156,f125])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    ~v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | spl3_3),
% 0.20/0.43    inference(resolution,[],[f152,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ~v3_pre_topc(u1_struct_0(sK0),sK0) | spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f91])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~v4_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(resolution,[],[f144,f74])).
% 0.20/0.44  fof(f144,plain,(
% 0.20/0.44    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(sK2,X0) | v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(superposition,[],[f61,f73])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.44  fof(f148,plain,(
% 0.20/0.44    spl3_6),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f147])).
% 0.20/0.44  fof(f147,plain,(
% 0.20/0.44    $false | spl3_6),
% 0.20/0.44    inference(resolution,[],[f129,f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    l1_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f40])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | spl3_6),
% 0.20/0.44    inference(resolution,[],[f119,f60])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    ~l1_struct_0(sK0) | spl3_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f117])).
% 0.20/0.44  fof(f146,plain,(
% 0.20/0.44    spl3_8),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.44  fof(f145,plain,(
% 0.20/0.44    $false | spl3_8),
% 0.20/0.44    inference(resolution,[],[f127,f44])).
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | spl3_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f125])).
% 0.20/0.44  fof(f143,plain,(
% 0.20/0.44    spl3_7),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.44  fof(f142,plain,(
% 0.20/0.44    $false | spl3_7),
% 0.20/0.44    inference(resolution,[],[f123,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    v2_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f40])).
% 0.20/0.44  fof(f123,plain,(
% 0.20/0.44    ~v2_pre_topc(sK0) | spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f121])).
% 0.20/0.44  fof(f141,plain,(
% 0.20/0.44    spl3_10),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.44  fof(f140,plain,(
% 0.20/0.44    $false | spl3_10),
% 0.20/0.44    inference(resolution,[],[f138,f71])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    v1_xboole_0(sK2)),
% 0.20/0.44    inference(definition_unfolding,[],[f52,f51])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f138,plain,(
% 0.20/0.44    ~v1_xboole_0(sK2) | spl3_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f136])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    ~spl3_6 | ~spl3_7 | ~spl3_8 | spl3_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f115,f102,f125,f121,f117])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_struct_0(sK0) | spl3_5),
% 0.20/0.44    inference(resolution,[],[f78,f103])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    ~v4_pre_topc(u1_struct_0(sK0),sK0) | spl3_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f102])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.44    inference(superposition,[],[f65,f59])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (428)------------------------------
% 0.20/0.44  % (428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (428)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (428)Memory used [KB]: 6268
% 0.20/0.44  % (428)Time elapsed: 0.045 s
% 0.20/0.44  % (428)------------------------------
% 0.20/0.44  % (428)------------------------------
% 0.20/0.44  % (423)Success in time 0.096 s
%------------------------------------------------------------------------------
