%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 169 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  453 ( 731 expanded)
%              Number of equality atoms :   35 (  64 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f91,f95,f101,f114,f148])).

fof(f148,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f146,f39])).

fof(f39,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f146,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f143,f113])).

fof(f113,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f143,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(resolution,[],[f121,f94])).

fof(f94,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_8
  <=> m2_orders_2(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(k1_xboole_0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(superposition,[],[f97,f113])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK4(sK0,sK1),X0)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(resolution,[],[f72,f94])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f71,f42])).

fof(f42,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f70,f58])).

fof(f58,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f69,f54])).

fof(f54,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f68,f50])).

fof(f50,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f46,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

fof(f62,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f114,plain,
    ( spl5_10
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f110,f99,f89,f112])).

fof(f89,plain,
    ( spl5_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f99,plain,
    ( spl5_9
  <=> r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f110,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f109,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f109,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl5_9 ),
    inference(resolution,[],[f100,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 != k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f100,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl5_9
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f96,f93,f61,f57,f53,f49,f45,f41,f99])).

fof(f96,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(resolution,[],[f82,f94])).

fof(f82,plain,
    ( ! [X2] :
        ( ~ m2_orders_2(X2,sK0,sK1)
        | r2_hidden(X2,k4_orders_2(sK0,sK1)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | r2_hidden(X2,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f80,f58])).

fof(f80,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | r2_hidden(X2,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f79,f54])).

fof(f79,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | r2_hidden(X2,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f78,f50])).

fof(f78,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | r2_hidden(X2,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f66,f46])).

fof(f66,plain,
    ( ! [X2] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | r2_hidden(X2,k4_orders_2(sK0,sK1)) )
    | ~ spl5_6 ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f95,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f77,f61,f57,f53,f49,f45,f41,f93])).

fof(f77,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,
    ( v2_struct_0(sK0)
    | m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f75,f58])).

fof(f75,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f74,f54])).

fof(f74,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f73,f50])).

fof(f73,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f65,f46])).

fof(f65,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f91,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f89])).

fof(f20,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f63,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f19,f61])).

fof(f19,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:35:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (8908)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (8914)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (8908)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f91,f95,f101,f114,f148])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f147])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_10)),
% 0.21/0.47    inference(subsumption_resolution,[],[f146,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    inference(equality_resolution,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f143,f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    k1_xboole_0 = sK4(sK0,sK1) | ~spl5_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl5_10 <=> k1_xboole_0 = sK4(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_10)),
% 0.21/0.47    inference(resolution,[],[f121,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl5_8 <=> m2_orders_2(sK4(sK0,sK1),sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(k1_xboole_0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_10)),
% 0.21/0.47    inference(superposition,[],[f97,f113])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK4(sK0,sK1),X0) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.47    inference(resolution,[],[f72,f94])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f71,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl5_2 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | ~spl5_6),
% 0.21/0.47    inference(resolution,[],[f62,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X2,X0,X1) | ~m2_orders_2(X3,X0,X1) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl5_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl5_10 | ~spl5_7 | ~spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f110,f99,f89,f112])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl5_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl5_9 <=> r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    k1_xboole_0 = sK4(sK0,sK1) | (~spl5_7 | ~spl5_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f109,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    k1_xboole_0 = sK4(sK0,sK1) | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1)) | ~spl5_9),
% 0.21/0.47    inference(resolution,[],[f100,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2 | k1_xboole_0 != k3_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.21/0.47    inference(rectify,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | ~spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f99])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl5_9 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f96,f93,f61,f57,f53,f49,f45,f41,f99])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.47    inference(resolution,[],[f82,f94])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X2] : (~m2_orders_2(X2,sK0,sK1) | r2_hidden(X2,k4_orders_2(sK0,sK1))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f42])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X2] : (v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | r2_hidden(X2,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f58])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | r2_hidden(X2,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f79,f54])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X2] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | r2_hidden(X2,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f78,f50])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X2] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | r2_hidden(X2,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f66,f46])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | r2_hidden(X2,k4_orders_2(sK0,sK1))) ) | ~spl5_6),
% 0.21/0.47    inference(resolution,[],[f62,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl5_8 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f77,f61,f57,f53,f49,f45,f41,f93])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f42])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    v2_struct_0(sK0) | m2_orders_2(sK4(sK0,sK1),sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f58])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(sK4(sK0,sK1),sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f54])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(sK4(sK0,sK1),sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f50])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(sK4(sK0,sK1),sK0,sK1) | (~spl5_2 | ~spl5_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f46])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(sK4(sK0,sK1),sK0,sK1) | ~spl5_6),
% 0.21/0.47    inference(resolution,[],[f62,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | m2_orders_2(sK4(X0,X1),X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f89])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl5_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f61])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f57])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    l1_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v5_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v4_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f45])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v3_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (8908)------------------------------
% 0.21/0.47  % (8908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8908)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (8908)Memory used [KB]: 6268
% 0.21/0.47  % (8908)Time elapsed: 0.053 s
% 0.21/0.47  % (8908)------------------------------
% 0.21/0.47  % (8908)------------------------------
% 0.21/0.47  % (8905)Success in time 0.111 s
%------------------------------------------------------------------------------
