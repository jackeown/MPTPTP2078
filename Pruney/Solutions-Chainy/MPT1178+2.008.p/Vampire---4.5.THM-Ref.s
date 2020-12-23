%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 408 expanded)
%              Number of leaves         :   28 ( 148 expanded)
%              Depth                    :   28
%              Number of atoms          :  882 (1708 expanded)
%              Number of equality atoms :   29 (  80 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f84,f89,f94,f99,f138,f147,f148,f154,f164,f168,f185,f211,f220,f221,f250,f252])).

fof(f252,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f241,f106])).

fof(f106,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f104,f83])).

fof(f83,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_xboole_0,X0)
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl6_7 ),
    inference(superposition,[],[f103,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_7
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f241,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(resolution,[],[f239,f184])).

fof(f184,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_14
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f238,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_16
  <=> k1_xboole_0 = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f237,f58])).

fof(f58,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f236,f93])).

fof(f93,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_8
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1))
        | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f235,f78])).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1))
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f234,f73])).

fof(f73,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f233,f68])).

fof(f68,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f231,f63])).

fof(f63,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK4(sK0,sK1))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f230,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f229,f58])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f228,f78])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f227,f73])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f226,f68])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f225,f63])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f36,f93])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f250,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f248,f106])).

fof(f248,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f247,f219])).

fof(f247,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f246,f58])).

fof(f246,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f245,f93])).

fof(f245,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f244,f78])).

fof(f244,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f243,f73])).

fof(f243,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f242,f68])).

fof(f242,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f240,f63])).

fof(f240,plain,
    ( ~ r1_xboole_0(sK4(sK0,sK1),k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(resolution,[],[f239,f45])).

fof(f221,plain,
    ( spl6_16
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f214,f208,f217])).

fof(f208,plain,
    ( spl6_15
  <=> r1_tarski(sK4(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f214,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f213,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f213,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK0,sK1))
    | k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl6_15 ),
    inference(resolution,[],[f210,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f210,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f220,plain,
    ( spl6_16
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f212,f208,f217])).

fof(f212,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl6_15 ),
    inference(resolution,[],[f210,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f35])).

fof(f211,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f206,f96,f91,f76,f71,f66,f61,f56,f208])).

fof(f96,plain,
    ( spl6_9
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f206,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f205,f58])).

fof(f205,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f204,f93])).

fof(f204,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f203,f78])).

fof(f203,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f202,f73])).

fof(f202,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f201,f68])).

fof(f201,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f199,f63])).

fof(f199,plain,
    ( r1_tarski(sK4(sK0,sK1),k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f194,f45])).

fof(f194,plain,
    ( ! [X2] :
        ( ~ m2_orders_2(X2,sK0,sK1)
        | r1_tarski(X2,k1_xboole_0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f191,f102])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
        | r1_tarski(X1,k1_xboole_0) )
    | ~ spl6_9 ),
    inference(superposition,[],[f43,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f191,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k4_orders_2(sK0,sK1))
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f190,f58])).

fof(f190,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f189,f78])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f188,f73])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f187,f68])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f186,f63])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_8 ),
    inference(resolution,[],[f52,f93])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
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
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f185,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f175,f151,f91,f76,f71,f66,f61,f56,f182])).

fof(f151,plain,
    ( spl6_13
  <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f175,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(resolution,[],[f174,f153])).

fof(f153,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | m2_orders_2(X0,sK0,sK1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f173,f58])).

fof(f173,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f172,f78])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f171,f73])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f170,f68])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f169,f63])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_8 ),
    inference(resolution,[],[f51,f93])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,
    ( ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f167,f151,f131])).

fof(f131,plain,
    ( spl6_10
  <=> v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f167,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_13 ),
    inference(resolution,[],[f153,f42])).

fof(f164,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f162,f133])).

fof(f133,plain,
    ( v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f162,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f161,f58])).

fof(f161,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f160,f78])).

fof(f160,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f159,f73])).

fof(f159,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f158,f68])).

fof(f158,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f157,f63])).

fof(f157,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f44,f93])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f154,plain,
    ( spl6_10
    | spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f149,f144,f151,f131])).

fof(f144,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f149,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_12 ),
    inference(superposition,[],[f41,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f148,plain,
    ( spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f141,f135,f144])).

fof(f135,plain,
    ( spl6_11
  <=> r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f141,plain,
    ( k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f140,f35])).

fof(f140,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k4_orders_2(sK0,sK1)))
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))
    | ~ spl6_11 ),
    inference(resolution,[],[f137,f50])).

fof(f137,plain,
    ( r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f147,plain,
    ( spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f139,f135,f144])).

fof(f139,plain,
    ( k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))
    | ~ spl6_11 ),
    inference(resolution,[],[f137,f107])).

fof(f138,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f118,f96,f135,f131])).

fof(f118,plain,
    ( r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f102,f41])).

fof(f99,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f27,f96])).

fof(f27,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f94,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f26,f91])).

fof(f26,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f84,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f79,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (26659)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.46  % (26638)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.48  % (26633)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.48  % (26638)Refutation not found, incomplete strategy% (26638)------------------------------
% 0.22/0.48  % (26638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26638)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26638)Memory used [KB]: 10618
% 0.22/0.48  % (26638)Time elapsed: 0.094 s
% 0.22/0.48  % (26638)------------------------------
% 0.22/0.48  % (26638)------------------------------
% 0.22/0.49  % (26659)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f84,f89,f94,f99,f138,f147,f148,f154,f164,f168,f185,f211,f220,f221,f250,f252])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_14 | ~spl6_16),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f251])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_14 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f241,f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl6_6 | ~spl6_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl6_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | ~v1_xboole_0(k1_xboole_0)) ) | ~spl6_7),
% 0.22/0.49    inference(superposition,[],[f103,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl6_7 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(resolution,[],[f46,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_14 | ~spl6_16)),
% 0.22/0.49    inference(resolution,[],[f239,f184])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f182])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl6_14 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(forward_demodulation,[],[f238,f219])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    k1_xboole_0 = sK4(sK0,sK1) | ~spl6_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f217])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl6_16 <=> k1_xboole_0 = sK4(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f237,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl6_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1)) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f236,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl6_8 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1)) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f235,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    l1_orders_2(sK0) | ~spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl6_5 <=> l1_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1)) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f234,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    v5_orders_2(sK0) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl6_4 <=> v5_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f233,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v4_orders_2(sK0) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl6_3 <=> v4_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f231,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v3_orders_2(sK0) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl6_2 <=> v3_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK4(sK0,sK1)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(resolution,[],[f230,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f229,f58])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f228,f78])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f227,f73])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f226,f68])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl6_2 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f225,f63])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | ~spl6_8),
% 0.22/0.49    inference(resolution,[],[f36,f93])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X2,X0,X1) | ~m2_orders_2(X3,X0,X1) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_16),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f249])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f248,f106])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(forward_demodulation,[],[f247,f219])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f246,f58])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f245,f93])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f244,f78])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f243,f73])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f242,f68])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f240,f63])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ~r1_xboole_0(sK4(sK0,sK1),k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16)),
% 0.22/0.49    inference(resolution,[],[f239,f45])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    spl6_16 | ~spl6_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f214,f208,f217])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    spl6_15 <=> r1_tarski(sK4(sK0,sK1),k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    k1_xboole_0 = sK4(sK0,sK1) | ~spl6_15),
% 0.22/0.49    inference(subsumption_resolution,[],[f213,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK4(sK0,sK1)) | k1_xboole_0 = sK4(sK0,sK1) | ~spl6_15),
% 0.22/0.49    inference(resolution,[],[f210,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | ~spl6_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    spl6_16 | ~spl6_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f212,f208,f217])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    k1_xboole_0 = sK4(sK0,sK1) | ~spl6_15),
% 0.22/0.50    inference(resolution,[],[f210,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(resolution,[],[f50,f35])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    spl6_15 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f206,f96,f91,f76,f71,f66,f61,f56,f208])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl6_9 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f205,f58])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f204,f93])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f203,f78])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f202,f73])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f201,f68])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f199,f63])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    r1_tarski(sK4(sK0,sK1),k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(resolution,[],[f194,f45])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ( ! [X2] : (~m2_orders_2(X2,sK0,sK1) | r1_tarski(X2,k1_xboole_0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9)),
% 0.22/0.50    inference(resolution,[],[f191,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,k4_orders_2(sK0,sK1)) | r1_tarski(X1,k1_xboole_0)) ) | ~spl6_9),
% 0.22/0.50    inference(superposition,[],[f43,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k4_orders_2(sK0,sK1)) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f190,f58])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f189,f78])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f188,f73])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f187,f68])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f186,f63])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f52,f93])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    spl6_14 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f175,f151,f91,f76,f71,f66,f61,f56,f182])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl6_13 <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    m2_orders_2(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_13)),
% 0.22/0.50    inference(resolution,[],[f174,f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | ~spl6_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f151])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f173,f58])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(sK0) | m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f172,f78])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f171,f73])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f170,f68])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f63])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f51,f93])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ~spl6_10 | ~spl6_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f167,f151,f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl6_10 <=> v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl6_13),
% 0.22/0.50    inference(resolution,[],[f153,f42])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f163])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f162,f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl6_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f161,f58])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f160,f78])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f159,f73])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f158,f68])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f157,f63])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f44,f93])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v1_xboole_0(k4_orders_2(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    spl6_10 | spl6_13 | ~spl6_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f149,f144,f151,f131])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl6_12 <=> k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl6_12),
% 0.22/0.50    inference(superposition,[],[f41,f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f144])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl6_12 | ~spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f141,f135,f144])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl6_11 <=> r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) | ~spl6_11),
% 0.22/0.50    inference(subsumption_resolution,[],[f140,f35])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,sK3(k4_orders_2(sK0,sK1))) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) | ~spl6_11),
% 0.22/0.50    inference(resolution,[],[f137,f50])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0) | ~spl6_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f135])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl6_12 | ~spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f139,f135,f144])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) | ~spl6_11),
% 0.22/0.50    inference(resolution,[],[f137,f107])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl6_10 | spl6_11 | ~spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f118,f96,f135,f131])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0) | v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl6_9),
% 0.22/0.50    inference(resolution,[],[f102,f41])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f96])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f91])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f86])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f81])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f76])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f71])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f66])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    v4_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f61])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    v3_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f56])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (26659)------------------------------
% 0.22/0.50  % (26659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26659)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (26659)Memory used [KB]: 1663
% 0.22/0.50  % (26659)Time elapsed: 0.083 s
% 0.22/0.50  % (26659)------------------------------
% 0.22/0.50  % (26659)------------------------------
% 0.22/0.50  % (26655)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (26648)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (26626)Success in time 0.141 s
%------------------------------------------------------------------------------
