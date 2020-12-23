%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 267 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  721 (1174 expanded)
%              Number of equality atoms :   67 ( 130 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f81,f85,f89,f109,f122,f134,f140,f144,f148,f157,f170,f188,f194,f251,f265,f280])).

fof(f280,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f278,f76])).

fof(f76,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f278,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f277,f72])).

fof(f72,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f277,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f276,f68])).

fof(f68,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f276,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f275,f64])).

fof(f64,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f275,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f274,f60])).

fof(f60,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f274,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f273,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f273,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f270,f169])).

fof(f169,plain,
    ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_24
  <=> r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f270,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(resolution,[],[f264,f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(o_0_0_xboole_0,X0,X1)
        | v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(o_0_0_xboole_0,X0,X1)
        | v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f264,plain,
    ( ! [X0] :
        ( m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_36
  <=> ! [X0] :
        ( m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f265,plain,
    ( spl6_36
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f252,f249,f75,f263])).

fof(f249,plain,
    ( spl6_34
  <=> ! [X1,X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f252,plain,
    ( ! [X0] :
        ( m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(resolution,[],[f250,f76])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f249])).

fof(f251,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f208,f192,f71,f67,f63,f59,f55,f249])).

fof(f192,plain,
    ( spl6_26
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | m2_orders_2(X3,X0,X1)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f207,f56])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f206,f68])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f205,f64])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f204,f60])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X1,sK0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(resolution,[],[f193,f72])).

fof(f193,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | m2_orders_2(X3,X0,X1)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f52,f192])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f188,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f186,f56])).

fof(f186,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f185,f76])).

fof(f185,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f184,f72])).

fof(f184,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f183,f68])).

fof(f183,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f182,f64])).

fof(f182,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f181,f60])).

fof(f181,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f180,f84])).

fof(f84,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f180,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(superposition,[],[f139,f153])).

fof(f153,plain,
    ( o_0_0_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_20
  <=> o_0_0_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k4_orders_2(X0,X1))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f170,plain,
    ( spl6_20
    | spl6_24
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f162,f155,f120,f168,f152])).

fof(f120,plain,
    ( spl6_13
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | r2_hidden(sK5(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

% (670)Refutation not found, incomplete strategy% (670)------------------------------
% (670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (670)Termination reason: Refutation not found, incomplete strategy

% (670)Memory used [KB]: 6268
% (670)Time elapsed: 0.040 s
% (670)------------------------------
% (670)------------------------------
fof(f155,plain,
    ( spl6_21
  <=> o_0_0_xboole_0 = sK5(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f162,plain,
    ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))
    | o_0_0_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_13
    | ~ spl6_21 ),
    inference(superposition,[],[f121,f156])).

fof(f156,plain,
    ( o_0_0_xboole_0 = sK5(k4_orders_2(sK0,sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f121,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f157,plain,
    ( spl6_20
    | spl6_21
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f149,f142,f120,f155,f152])).

fof(f142,plain,
    ( spl6_18
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f149,plain,
    ( o_0_0_xboole_0 = sK5(k4_orders_2(sK0,sK1))
    | o_0_0_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(resolution,[],[f143,f121])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f148,plain,
    ( spl6_19
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f105,f87,f83,f146])).

fof(f87,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(o_0_0_xboole_0,X0,X1)
        | v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f104,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
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
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(o_0_0_xboole_0,X0,X1)
        | ~ v6_orders_2(o_0_0_xboole_0,X0)
        | v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f103,f90])).

fof(f90,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f88,f84])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v6_orders_2(o_0_0_xboole_0,X0)
        | v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f98,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ v6_orders_2(o_0_0_xboole_0,X0)
        | v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f51,f90])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
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
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f144,plain,
    ( spl6_18
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f136,f132,f107,f142])).

fof(f107,plain,
    ( spl6_10
  <=> o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f132,plain,
    ( spl6_16
  <=> ! [X0,X2] :
        ( o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 != k3_tarski(X0)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f136,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 != o_0_0_xboole_0
        | o_0_0_xboole_0 = X0
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(superposition,[],[f133,f108])).

fof(f108,plain,
    ( o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f133,plain,
    ( ! [X2,X0] :
        ( o_0_0_xboole_0 != k3_tarski(X0)
        | o_0_0_xboole_0 = X2
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f140,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f48,f138])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f134,plain,
    ( spl6_16
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f102,f87,f83,f132])).

fof(f102,plain,
    ( ! [X2,X0] :
        ( o_0_0_xboole_0 = X2
        | o_0_0_xboole_0 != k3_tarski(X0)
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f93,f90])).

fof(f93,plain,
    ( ! [X2,X0] :
        ( o_0_0_xboole_0 != k3_tarski(X0)
        | k1_xboole_0 = X2
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f35,f90])).

fof(f35,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 != k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
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

fof(f122,plain,
    ( spl6_13
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f97,f87,f83,f120])).

fof(f97,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | r2_hidden(sK5(X0),X0) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f47,f90])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f109,plain,
    ( spl6_10
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f99,f87,f83,f79,f107])).

fof(f79,plain,
    ( spl6_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f99,plain,
    ( o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f80,f90])).

fof(f80,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f89,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f85,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f81,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f26,f79])).

fof(f26,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f77,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f25,f75])).

fof(f25,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (658)Refutation not found, incomplete strategy% (658)------------------------------
% 0.22/0.47  % (658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (666)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (658)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (658)Memory used [KB]: 10618
% 0.22/0.47  % (658)Time elapsed: 0.054 s
% 0.22/0.47  % (658)------------------------------
% 0.22/0.47  % (658)------------------------------
% 0.22/0.48  % (656)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (662)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (656)Refutation not found, incomplete strategy% (656)------------------------------
% 0.22/0.48  % (656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (656)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (656)Memory used [KB]: 10618
% 0.22/0.48  % (656)Time elapsed: 0.072 s
% 0.22/0.48  % (656)------------------------------
% 0.22/0.48  % (656)------------------------------
% 0.22/0.48  % (666)Refutation not found, incomplete strategy% (666)------------------------------
% 0.22/0.48  % (666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (666)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (666)Memory used [KB]: 10618
% 0.22/0.48  % (666)Time elapsed: 0.063 s
% 0.22/0.48  % (666)------------------------------
% 0.22/0.48  % (666)------------------------------
% 0.22/0.48  % (667)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (664)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (670)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (676)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (674)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (667)Refutation not found, incomplete strategy% (667)------------------------------
% 0.22/0.49  % (667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (667)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (667)Memory used [KB]: 6268
% 0.22/0.49  % (667)Time elapsed: 0.077 s
% 0.22/0.49  % (667)------------------------------
% 0.22/0.49  % (667)------------------------------
% 0.22/0.49  % (664)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f81,f85,f89,f109,f122,f134,f140,f144,f148,f157,f170,f188,f194,f251,f265,f280])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_24 | ~spl6_36),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f278,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl6_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f277,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    l1_orders_2(sK0) | ~spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl6_5 <=> l1_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f276,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v5_orders_2(sK0) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl6_4 <=> v5_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f275,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    v4_orders_2(sK0) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl6_3 <=> v4_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f274,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    v3_orders_2(sK0) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl6_2 <=> v3_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f273,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl6_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (~spl6_19 | ~spl6_24 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f270,f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) | ~spl6_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f168])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    spl6_24 <=> r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    ~r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (~spl6_19 | ~spl6_36)),
% 0.22/0.49    inference(resolution,[],[f264,f147])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(o_0_0_xboole_0,X0,X1) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) ) | ~spl6_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f146])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    spl6_19 <=> ! [X1,X0] : (~m2_orders_2(o_0_0_xboole_0,X0,X1) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    ( ! [X0] : (m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | ~spl6_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    spl6_36 <=> ! [X0] : (m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.49  fof(f265,plain,(
% 0.22/0.49    spl6_36 | ~spl6_6 | ~spl6_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f252,f249,f75,f263])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    spl6_34 <=> ! [X1,X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    ( ! [X0] : (m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_6 | ~spl6_34)),
% 0.22/0.49    inference(resolution,[],[f250,f76])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) ) | ~spl6_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f249])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    spl6_34 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f208,f192,f71,f67,f63,f59,f55,f249])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl6_26 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f207,f56])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f68])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f205,f64])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_5 | ~spl6_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f204,f60])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl6_5 | ~spl6_26)),
% 0.22/0.49    inference(resolution,[],[f193,f72])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) ) | ~spl6_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f192])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    spl6_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f192])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_20),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f187])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f186,f56])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f185,f76])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f184,f72])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f183,f68])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f182,f64])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f181,f60])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_8 | ~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f180,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    v1_xboole_0(o_0_0_xboole_0) | ~spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl6_8 <=> v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ~v1_xboole_0(o_0_0_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_17 | ~spl6_20)),
% 0.22/0.49    inference(superposition,[],[f139,f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k4_orders_2(sK0,sK1) | ~spl6_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f152])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl6_20 <=> o_0_0_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl6_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl6_17 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl6_20 | spl6_24 | ~spl6_13 | ~spl6_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f162,f155,f120,f168,f152])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl6_13 <=> ! [X0] : (o_0_0_xboole_0 = X0 | r2_hidden(sK5(X0),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.49  % (670)Refutation not found, incomplete strategy% (670)------------------------------
% 0.22/0.49  % (670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (670)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (670)Memory used [KB]: 6268
% 0.22/0.49  % (670)Time elapsed: 0.040 s
% 0.22/0.49  % (670)------------------------------
% 0.22/0.49  % (670)------------------------------
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl6_21 <=> o_0_0_xboole_0 = sK5(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) | o_0_0_xboole_0 = k4_orders_2(sK0,sK1) | (~spl6_13 | ~spl6_21)),
% 0.22/0.49    inference(superposition,[],[f121,f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    o_0_0_xboole_0 = sK5(k4_orders_2(sK0,sK1)) | ~spl6_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(X0),X0) | o_0_0_xboole_0 = X0) ) | ~spl6_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f120])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    spl6_20 | spl6_21 | ~spl6_13 | ~spl6_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f149,f142,f120,f155,f152])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl6_18 <=> ! [X0] : (o_0_0_xboole_0 = X0 | ~r2_hidden(X0,k4_orders_2(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    o_0_0_xboole_0 = sK5(k4_orders_2(sK0,sK1)) | o_0_0_xboole_0 = k4_orders_2(sK0,sK1) | (~spl6_13 | ~spl6_18)),
% 0.22/0.49    inference(resolution,[],[f143,f121])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | o_0_0_xboole_0 = X0) ) | ~spl6_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    spl6_19 | ~spl6_8 | ~spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f105,f87,f83,f146])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl6_9 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(o_0_0_xboole_0,X0,X1) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(o_0_0_xboole_0,X0,X1) | ~v6_orders_2(o_0_0_xboole_0,X0) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f103,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k1_xboole_0 | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(resolution,[],[f88,f84])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl6_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v6_orders_2(o_0_0_xboole_0,X0) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f98,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v6_orders_2(o_0_0_xboole_0,X0) | v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f51,f90])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    spl6_18 | ~spl6_10 | ~spl6_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f136,f132,f107,f142])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl6_10 <=> o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl6_16 <=> ! [X0,X2] : (o_0_0_xboole_0 = X2 | o_0_0_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_10 | ~spl6_16)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ( ! [X0] : (o_0_0_xboole_0 != o_0_0_xboole_0 | o_0_0_xboole_0 = X0 | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_10 | ~spl6_16)),
% 0.22/0.49    inference(superposition,[],[f133,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ( ! [X2,X0] : (o_0_0_xboole_0 != k3_tarski(X0) | o_0_0_xboole_0 = X2 | ~r2_hidden(X2,X0)) ) | ~spl6_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f132])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    spl6_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f138])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl6_16 | ~spl6_8 | ~spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f102,f87,f83,f132])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ( ! [X2,X0] : (o_0_0_xboole_0 = X2 | o_0_0_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0)) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f93,f90])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X2,X0] : (o_0_0_xboole_0 != k3_tarski(X0) | k1_xboole_0 = X2 | ~r2_hidden(X2,X0)) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f35,f90])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.22/0.49    inference(rectify,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl6_13 | ~spl6_8 | ~spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f97,f87,f83,f120])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ( ! [X0] : (o_0_0_xboole_0 = X0 | r2_hidden(sK5(X0),X0)) ) | (~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f47,f90])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl6_10 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f99,f87,f83,f79,f107])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl6_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | (~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f80,f90])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f87])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f83])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f79])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f75])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f71])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl6_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f67])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f63])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f59])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f55])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (664)------------------------------
% 0.22/0.49  % (664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (664)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (664)Memory used [KB]: 10746
% 0.22/0.49  % (664)Time elapsed: 0.085 s
% 0.22/0.49  % (664)------------------------------
% 0.22/0.49  % (664)------------------------------
% 0.22/0.49  % (654)Success in time 0.134 s
%------------------------------------------------------------------------------
