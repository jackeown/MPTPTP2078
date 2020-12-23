%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 434 expanded)
%              Number of leaves         :   22 ( 154 expanded)
%              Depth                    :   22
%              Number of atoms          :  897 (2043 expanded)
%              Number of equality atoms :   72 ( 199 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14487)Termination reason: Refutation not found, incomplete strategy

fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f109,f114,f131,f144,f215,f231,f241,f269,f283])).

fof(f283,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_15
    | spl7_17
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_15
    | spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f281,f229])).

fof(f229,plain,
    ( k1_xboole_0 != k4_orders_2(sK0,sK1)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl7_17
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f281,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f280,f143])).

fof(f143,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl7_9
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f280,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f278,f214])).

fof(f214,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl7_15
  <=> r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f278,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(superposition,[],[f126,f240])).

fof(f240,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl7_18
  <=> k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,sK1,X0),X0)
        | ~ m2_orders_2(sK3(sK0,sK1,X0),sK0,sK1)
        | k4_orders_2(sK0,sK1) = X0 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f100,f108])).

fof(f108,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f100,plain,
    ( ! [X8,X7] :
        ( ~ m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(sK3(sK0,X7,X8),sK0,X7)
        | ~ r2_hidden(sK3(sK0,X7,X8),X8)
        | k4_orders_2(sK0,X7) = X8 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f99,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f99,plain,
    ( ! [X8,X7] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(sK3(sK0,X7,X8),sK0,X7)
        | ~ r2_hidden(sK3(sK0,X7,X8),X8)
        | k4_orders_2(sK0,X7) = X8 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f98,f68])).

fof(f68,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f98,plain,
    ( ! [X8,X7] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(sK3(sK0,X7,X8),sK0,X7)
        | ~ r2_hidden(sK3(sK0,X7,X8),X8)
        | k4_orders_2(sK0,X7) = X8 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f97,f63])).

fof(f63,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f97,plain,
    ( ! [X8,X7] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(sK3(sK0,X7,X8),sK0,X7)
        | ~ r2_hidden(sK3(sK0,X7,X8),X8)
        | k4_orders_2(sK0,X7) = X8 )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f79,f58])).

fof(f58,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f79,plain,
    ( ! [X8,X7] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(sK3(sK0,X7,X8),sK0,X7)
        | ~ r2_hidden(sK3(sK0,X7,X8),X8)
        | k4_orders_2(sK0,X7) = X8 )
    | ~ spl7_5 ),
    inference(resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_orders_2(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(f73,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f269,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f267,f53])).

fof(f267,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f266,f108])).

fof(f266,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f265,f73])).

fof(f265,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f264,f68])).

fof(f264,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f263,f63])).

fof(f263,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f262,f58])).

fof(f262,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f259,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f259,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_17 ),
    inference(superposition,[],[f44,f230])).

fof(f230,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f241,plain,
    ( spl7_18
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f236,f224,f238])).

fof(f224,plain,
    ( spl7_16
  <=> r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f236,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f233,f33])).

fof(f33,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f233,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0)
    | k1_xboole_0 != k3_tarski(k1_xboole_0)
    | ~ spl7_16 ),
    inference(resolution,[],[f226,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 != k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(f226,plain,
    ( r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f224])).

fof(f231,plain,
    ( spl7_16
    | spl7_17
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f221,f212,f141,f111,f106,f71,f66,f61,f56,f51,f228,f224])).

fof(f111,plain,
    ( spl7_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f221,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(resolution,[],[f214,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k4_orders_2(sK0,sK1) = X0
        | r2_hidden(sK3(sK0,sK1,X0),X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f181,f143])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
        | k4_orders_2(sK0,sK1) = X0
        | r2_hidden(sK3(sK0,sK1,X0),X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
        | k4_orders_2(sK0,sK1) = X0
        | r2_hidden(sK3(sK0,sK1,X0),X0)
        | k4_orders_2(sK0,sK1) = X0 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f126,f125])).

fof(f125,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK3(sK0,sK1,X1)
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | k4_orders_2(sK0,sK1) = X1 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f122,f108])).

fof(f122,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK3(sK0,sK1,X1)
        | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | k4_orders_2(sK0,sK1) = X1 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f119,f96])).

fof(f96,plain,
    ( ! [X6,X5] :
        ( m2_orders_2(sK3(sK0,X5,X6),sK0,X5)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(sK3(sK0,X5,X6),X6)
        | k4_orders_2(sK0,X5) = X6 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,
    ( ! [X6,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X5,X6),sK0,X5)
        | r2_hidden(sK3(sK0,X5,X6),X6)
        | k4_orders_2(sK0,X5) = X6 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f94,f68])).

fof(f94,plain,
    ( ! [X6,X5] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X5,X6),sK0,X5)
        | r2_hidden(sK3(sK0,X5,X6),X6)
        | k4_orders_2(sK0,X5) = X6 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f93,f63])).

fof(f93,plain,
    ( ! [X6,X5] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X5,X6),sK0,X5)
        | r2_hidden(sK3(sK0,X5,X6),X6)
        | k4_orders_2(sK0,X5) = X6 )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f78,f58])).

fof(f78,plain,
    ( ! [X6,X5] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X5,X6),sK0,X5)
        | r2_hidden(sK3(sK0,X5,X6),X6)
        | k4_orders_2(sK0,X5) = X6 )
    | ~ spl7_5 ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(sK3(X0,X1,X2),X0,X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_orders_2(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | k1_xboole_0 = X0 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f118,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f116,f36])).

fof(f116,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k4_orders_2(sK0,sK1))
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f108])).

fof(f88,plain,
    ( ! [X2,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f87,f53])).

fof(f87,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f86,f68])).

fof(f86,plain,
    ( ! [X2,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f85,f63])).

fof(f85,plain,
    ( ! [X2,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f76,f58])).

fof(f76,plain,
    ( ! [X2,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl7_5 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f215,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f209,f141,f111,f106,f71,f66,f61,f56,f51,f212])).

fof(f209,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f208,f143])).

fof(f208,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f207,f33])).

fof(f207,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(condensation,[],[f206])).

fof(f206,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,k1_xboole_0)
        | ~ m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,k1_xboole_0)
        | ~ m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(superposition,[],[f132,f177])).

fof(f177,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK6(k1_xboole_0,X0)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f174,f143])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | k1_xboole_0 = sK6(k1_xboole_0,X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f139,f33])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(k3_tarski(X0),sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | k1_xboole_0 = sK6(X0,X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f138,f119])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(k3_tarski(X0),sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | k1_xboole_0 = sK6(X0,X1)
        | k1_xboole_0 != k3_tarski(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f132,f36])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X1,X0),X1)
        | ~ m2_orders_2(k3_tarski(X1),sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f117,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f104,f108])).

fof(f104,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | ~ m2_orders_2(X11,sK0,X9)
        | ~ r1_xboole_0(X10,X11) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f103,f53])).

fof(f103,plain,
    ( ! [X10,X11,X9] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | ~ m2_orders_2(X11,sK0,X9)
        | ~ r1_xboole_0(X10,X11) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f102,f68])).

fof(f102,plain,
    ( ! [X10,X11,X9] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | ~ m2_orders_2(X11,sK0,X9)
        | ~ r1_xboole_0(X10,X11) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f101,f63])).

fof(f101,plain,
    ( ! [X10,X11,X9] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | ~ m2_orders_2(X11,sK0,X9)
        | ~ r1_xboole_0(X10,X11) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f80,f58])).

fof(f80,plain,
    ( ! [X10,X11,X9] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | ~ m2_orders_2(X11,sK0,X9)
        | ~ r1_xboole_0(X10,X11) )
    | ~ spl7_5 ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f144,plain,
    ( spl7_9
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f135,f128,f106,f71,f66,f61,f56,f51,f141])).

% (14480)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f128,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f135,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f134,f108])).

fof(f134,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(superposition,[],[f84,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK5(sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f84,plain,
    ( ! [X0] :
        ( m2_orders_2(sK5(sK0,X0),sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f83,f53])).

fof(f83,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK5(sK0,X0),sK0,X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f82,f68])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK5(sK0,X0),sK0,X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f81,f63])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK5(sK0,X0),sK0,X0) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f75,f58])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK5(sK0,X0),sK0,X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(sK5(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

% (14487)Memory used [KB]: 10618
% (14487)Time elapsed: 0.074 s
% (14487)------------------------------
% (14487)------------------------------
% (14480)Refutation not found, incomplete strategy% (14480)------------------------------
% (14480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14480)Termination reason: Refutation not found, incomplete strategy

% (14480)Memory used [KB]: 1663
% (14480)Time elapsed: 0.068 s
% (14480)------------------------------
% (14480)------------------------------
% (14481)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (14478)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (14473)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (14468)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (14477)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (14467)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (14468)Refutation not found, incomplete strategy% (14468)------------------------------
% (14468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14468)Termination reason: Refutation not found, incomplete strategy

% (14468)Memory used [KB]: 10618
% (14468)Time elapsed: 0.093 s
% (14468)------------------------------
% (14468)------------------------------
fof(f131,plain,
    ( spl7_8
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f123,f111,f106,f71,f66,f61,f56,f51,f128])).

fof(f123,plain,
    ( k1_xboole_0 = sK5(sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f120,f108])).

fof(f120,plain,
    ( k1_xboole_0 = sK5(sK0,sK1)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f119,f84])).

fof(f114,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f26,f111])).

fof(f26,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f109,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f25,f106])).

fof(f25,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (14472)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (14487)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (14470)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (14487)Refutation not found, incomplete strategy% (14487)------------------------------
% 0.20/0.48  % (14487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14470)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (14487)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f109,f114,f131,f144,f215,f231,f241,f269,f283])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_15 | spl7_17 | ~spl7_18),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f282])).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_15 | spl7_17 | ~spl7_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f281,f229])).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    k1_xboole_0 != k4_orders_2(sK0,sK1) | spl7_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f228])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    spl7_17 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    k1_xboole_0 = k4_orders_2(sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_15 | ~spl7_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f280,f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl7_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    spl7_9 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.49  fof(f280,plain,(
% 0.20/0.49    ~m2_orders_2(k1_xboole_0,sK0,sK1) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_15 | ~spl7_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f278,f214])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    r2_hidden(k1_xboole_0,k1_xboole_0) | ~spl7_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f212])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    spl7_15 <=> r2_hidden(k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    ~r2_hidden(k1_xboole_0,k1_xboole_0) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_18)),
% 0.20/0.49    inference(superposition,[],[f126,f240])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0) | ~spl7_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f238])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    spl7_18 <=> k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK3(sK0,sK1,X0),X0) | ~m2_orders_2(sK3(sK0,sK1,X0),sK0,sK1) | k4_orders_2(sK0,sK1) = X0) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.49    inference(resolution,[],[f100,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl7_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl7_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X8,X7] : (~m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(sK3(sK0,X7,X8),sK0,X7) | ~r2_hidden(sK3(sK0,X7,X8),X8) | k4_orders_2(sK0,X7) = X8) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f99,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    spl7_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X8,X7] : (v2_struct_0(sK0) | ~m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(sK3(sK0,X7,X8),sK0,X7) | ~r2_hidden(sK3(sK0,X7,X8),X8) | k4_orders_2(sK0,X7) = X8) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f98,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v5_orders_2(sK0) | ~spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl7_4 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X8,X7] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(sK3(sK0,X7,X8),sK0,X7) | ~r2_hidden(sK3(sK0,X7,X8),X8) | k4_orders_2(sK0,X7) = X8) ) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f97,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v4_orders_2(sK0) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl7_3 <=> v4_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X8,X7] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(sK3(sK0,X7,X8),sK0,X7) | ~r2_hidden(sK3(sK0,X7,X8),X8) | k4_orders_2(sK0,X7) = X8) ) | (~spl7_2 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f79,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    v3_orders_2(sK0) | ~spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl7_2 <=> v3_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X8,X7] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X7,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(sK3(sK0,X7,X8),sK0,X7) | ~r2_hidden(sK3(sK0,X7,X8),X8) | k4_orders_2(sK0,X7) = X8) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f73,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k4_orders_2(X0,X1) = X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    l1_orders_2(sK0) | ~spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl7_5 <=> l1_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f268])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f267,f53])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f266,f108])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f265,f73])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f264,f68])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f263,f63])).
% 0.20/0.49  fof(f263,plain,(
% 0.20/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl7_2 | ~spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f262,f58])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl7_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f259,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl7_17),
% 0.20/0.49    inference(superposition,[],[f44,f230])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl7_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f228])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    spl7_18 | ~spl7_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f236,f224,f238])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    spl7_16 <=> r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0) | ~spl7_16),
% 0.20/0.49    inference(subsumption_resolution,[],[f233,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    k1_xboole_0 = sK3(sK0,sK1,k1_xboole_0) | k1_xboole_0 != k3_tarski(k1_xboole_0) | ~spl7_16),
% 0.20/0.49    inference(resolution,[],[f226,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2 | k1_xboole_0 != k3_tarski(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.20/0.49    inference(rectify,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) | ~spl7_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f224])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    spl7_16 | spl7_17 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f221,f212,f141,f111,f106,f71,f66,f61,f56,f51,f228,f224])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl7_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    k1_xboole_0 = k4_orders_2(sK0,sK1) | r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9 | ~spl7_15)),
% 0.20/0.49    inference(resolution,[],[f214,f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k4_orders_2(sK0,sK1) = X0 | r2_hidden(sK3(sK0,sK1,X0),X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f181,f143])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | k4_orders_2(sK0,sK1) = X0 | r2_hidden(sK3(sK0,sK1,X0),X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | k4_orders_2(sK0,sK1) = X0 | r2_hidden(sK3(sK0,sK1,X0),X0) | k4_orders_2(sK0,sK1) = X0) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(superposition,[],[f126,f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = sK3(sK0,sK1,X1) | r2_hidden(sK3(sK0,sK1,X1),X1) | k4_orders_2(sK0,sK1) = X1) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f122,f108])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = sK3(sK0,sK1,X1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(sK3(sK0,sK1,X1),X1) | k4_orders_2(sK0,sK1) = X1) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(resolution,[],[f119,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X6,X5] : (m2_orders_2(sK3(sK0,X5,X6),sK0,X5) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(sK3(sK0,X5,X6),X6) | k4_orders_2(sK0,X5) = X6) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f95,f53])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X6,X5] : (v2_struct_0(sK0) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X5,X6),sK0,X5) | r2_hidden(sK3(sK0,X5,X6),X6) | k4_orders_2(sK0,X5) = X6) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f94,f68])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X6,X5] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X5,X6),sK0,X5) | r2_hidden(sK3(sK0,X5,X6),X6) | k4_orders_2(sK0,X5) = X6) ) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f93,f63])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X6,X5] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X5,X6),sK0,X5) | r2_hidden(sK3(sK0,X5,X6),X6) | k4_orders_2(sK0,X5) = X6) ) | (~spl7_2 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f58])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X6,X5] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X5,X6),sK0,X5) | r2_hidden(sK3(sK0,X5,X6),X6) | k4_orders_2(sK0,X5) = X6) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f73,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_orders_2(X0,X1) = X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | k1_xboole_0 = X0) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.49    inference(resolution,[],[f116,f36])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,k4_orders_2(sK0,sK1)) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.49    inference(resolution,[],[f88,f108])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f87,f53])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X2,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f86,f68])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f85,f63])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (~spl7_2 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f58])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f73,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    spl7_15 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f209,f141,f111,f106,f71,f66,f61,f56,f51,f212])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    r2_hidden(k1_xboole_0,k1_xboole_0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f208,f143])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ~m2_orders_2(k1_xboole_0,sK0,sK1) | r2_hidden(k1_xboole_0,k1_xboole_0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(forward_demodulation,[],[f207,f33])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    r2_hidden(k1_xboole_0,k1_xboole_0) | ~m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(condensation,[],[f206])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_xboole_0) | ~m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f204])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_xboole_0) | ~m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(superposition,[],[f132,f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f174,f143])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | k1_xboole_0 = sK6(k1_xboole_0,X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(superposition,[],[f139,f33])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m2_orders_2(k3_tarski(X0),sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | k1_xboole_0 = sK6(X0,X1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f138,f119])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m2_orders_2(k3_tarski(X0),sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | k1_xboole_0 = sK6(X0,X1) | k1_xboole_0 != k3_tarski(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.49    inference(resolution,[],[f132,f36])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK6(X1,X0),X1) | ~m2_orders_2(k3_tarski(X1),sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.49    inference(resolution,[],[f117,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.49    inference(resolution,[],[f104,f108])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | ~m2_orders_2(X11,sK0,X9) | ~r1_xboole_0(X10,X11)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f53])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | ~m2_orders_2(X11,sK0,X9) | ~r1_xboole_0(X10,X11)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f102,f68])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | ~m2_orders_2(X11,sK0,X9) | ~r1_xboole_0(X10,X11)) ) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f63])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | ~m2_orders_2(X11,sK0,X9) | ~r1_xboole_0(X10,X11)) ) | (~spl7_2 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f80,f58])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | ~m2_orders_2(X11,sK0,X9) | ~r1_xboole_0(X10,X11)) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f73,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m2_orders_2(X3,X0,X1) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    spl7_9 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f135,f128,f106,f71,f66,f61,f56,f51,f141])).
% 0.20/0.49  % (14480)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl7_8 <=> k1_xboole_0 = sK5(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    m2_orders_2(k1_xboole_0,sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f108])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    m2_orders_2(k1_xboole_0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_8)),
% 0.20/0.49    inference(superposition,[],[f84,f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    k1_xboole_0 = sK5(sK0,sK1) | ~spl7_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f128])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0] : (m2_orders_2(sK5(sK0,X0),sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f83,f53])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK5(sK0,X0),sK0,X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f82,f68])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK5(sK0,X0),sK0,X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f81,f63])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK5(sK0,X0),sK0,X0)) ) | (~spl7_2 | ~spl7_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f58])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK5(sK0,X0),sK0,X0)) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f73,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK5(X0,X1),X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.20/0.49  % (14487)Memory used [KB]: 10618
% 0.20/0.49  % (14487)Time elapsed: 0.074 s
% 0.20/0.49  % (14487)------------------------------
% 0.20/0.49  % (14487)------------------------------
% 0.20/0.49  % (14480)Refutation not found, incomplete strategy% (14480)------------------------------
% 0.20/0.49  % (14480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14480)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (14480)Memory used [KB]: 1663
% 0.20/0.49  % (14480)Time elapsed: 0.068 s
% 0.20/0.49  % (14480)------------------------------
% 0.20/0.49  % (14480)------------------------------
% 0.20/0.49  % (14481)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (14478)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (14473)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (14468)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (14477)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (14467)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (14468)Refutation not found, incomplete strategy% (14468)------------------------------
% 0.20/0.50  % (14468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14468)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (14468)Memory used [KB]: 10618
% 0.20/0.50  % (14468)Time elapsed: 0.093 s
% 0.20/0.50  % (14468)------------------------------
% 0.20/0.50  % (14468)------------------------------
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl7_8 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f123,f111,f106,f71,f66,f61,f56,f51,f128])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    k1_xboole_0 = sK5(sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f120,f108])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    k1_xboole_0 = sK5(sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.50    inference(resolution,[],[f119,f84])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl7_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f26,f111])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl7_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f25,f106])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl7_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f71])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f66])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f61])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f56])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f51])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (14470)------------------------------
% 0.20/0.50  % (14470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14470)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (14470)Memory used [KB]: 10746
% 0.20/0.50  % (14470)Time elapsed: 0.075 s
% 0.20/0.50  % (14470)------------------------------
% 0.20/0.50  % (14470)------------------------------
% 0.20/0.51  % (14466)Success in time 0.149 s
%------------------------------------------------------------------------------
