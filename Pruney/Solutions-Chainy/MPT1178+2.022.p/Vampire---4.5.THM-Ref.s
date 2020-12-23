%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 386 expanded)
%              Number of leaves         :   41 ( 170 expanded)
%              Depth                    :   13
%              Number of atoms          : 1019 (1711 expanded)
%              Number of equality atoms :   39 (  93 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f104,f112,f125,f140,f159,f163,f178,f182,f194,f198,f213,f227,f239,f245,f268,f342,f347,f353,f373,f377,f380,f406,f493,f507])).

fof(f507,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f505,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f505,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f504,f82])).

fof(f82,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f504,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f503,f78])).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl9_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f503,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f502,f74])).

fof(f74,plain,
    ( v5_orders_2(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl9_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f502,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f501,f70])).

fof(f70,plain,
    ( v4_orders_2(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl9_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f501,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f495,f66])).

fof(f66,plain,
    ( v3_orders_2(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl9_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f495,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_22
    | ~ spl9_61 ),
    inference(resolution,[],[f492,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( m2_orders_2(sK5(X0,X1),X0,X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f161])).

% (22273)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f161,plain,
    ( spl9_22
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | m2_orders_2(sK5(X0,X1),X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f492,plain,
    ( ! [X0] : ~ m2_orders_2(X0,sK0,sK1)
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl9_61
  <=> ! [X0] : ~ m2_orders_2(X0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f493,plain,
    ( spl9_61
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_28
    | ~ spl9_31
    | ~ spl9_50
    | spl9_51 ),
    inference(avatar_split_clause,[],[f453,f351,f345,f225,f196,f180,f97,f81,f77,f73,f69,f65,f61,f491])).

fof(f97,plain,
    ( spl9_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f180,plain,
    ( spl9_25
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f196,plain,
    ( spl9_28
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | m2_orders_2(X3,X0,X1)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f225,plain,
    ( spl9_31
  <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f345,plain,
    ( spl9_50
  <=> ! [X1,X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f351,plain,
    ( spl9_51
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f453,plain,
    ( ! [X0] : ~ m2_orders_2(X0,sK0,sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_28
    | ~ spl9_31
    | ~ spl9_50
    | spl9_51 ),
    inference(subsumption_resolution,[],[f449,f181])).

fof(f181,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f180])).

fof(f449,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_28
    | ~ spl9_31
    | ~ spl9_50
    | spl9_51 ),
    inference(backward_demodulation,[],[f348,f444])).

fof(f444,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_28
    | ~ spl9_31
    | spl9_51 ),
    inference(subsumption_resolution,[],[f443,f366])).

fof(f366,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_28
    | spl9_51 ),
    inference(subsumption_resolution,[],[f365,f62])).

fof(f365,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_28
    | spl9_51 ),
    inference(subsumption_resolution,[],[f364,f82])).

fof(f364,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_28
    | spl9_51 ),
    inference(subsumption_resolution,[],[f363,f78])).

fof(f363,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_28
    | spl9_51 ),
    inference(subsumption_resolution,[],[f362,f74])).

fof(f362,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_28
    | spl9_51 ),
    inference(subsumption_resolution,[],[f361,f70])).

fof(f361,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl9_2
    | ~ spl9_28
    | spl9_51 ),
    inference(subsumption_resolution,[],[f360,f66])).

fof(f360,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl9_28
    | spl9_51 ),
    inference(resolution,[],[f352,f197])).

fof(f197,plain,
    ( ! [X0,X3,X1] :
        ( m2_orders_2(X3,X0,X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f352,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl9_51 ),
    inference(avatar_component_clause,[],[f351])).

fof(f443,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl9_10
    | ~ spl9_31 ),
    inference(superposition,[],[f98,f226])).

fof(f226,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f225])).

fof(f98,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl9_6
    | ~ spl9_50 ),
    inference(resolution,[],[f346,f82])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f345])).

fof(f406,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f404,f62])).

fof(f404,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f403,f82])).

fof(f403,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f402,f78])).

fof(f402,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f401,f74])).

fof(f401,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f400,f70])).

fof(f400,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f399,f66])).

fof(f399,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f394,f181])).

fof(f394,plain,
    ( r2_hidden(sK5(sK0,sK1),k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(resolution,[],[f376,f162])).

fof(f376,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl9_54
  <=> ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ m2_orders_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f380,plain,
    ( spl9_25
    | ~ spl9_8
    | ~ spl9_30
    | ~ spl9_53 ),
    inference(avatar_split_clause,[],[f379,f371,f215,f89,f180])).

fof(f89,plain,
    ( spl9_8
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f215,plain,
    ( spl9_30
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f371,plain,
    ( spl9_53
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_tarski(X1))
        | ~ r1_tarski(X1,sK7(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f379,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_8
    | ~ spl9_30
    | ~ spl9_53 ),
    inference(forward_demodulation,[],[f378,f216])).

fof(f216,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f378,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_tarski(k1_xboole_0))
    | ~ spl9_8
    | ~ spl9_53 ),
    inference(resolution,[],[f372,f90])).

fof(f90,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK7(X1,X0))
        | ~ r2_hidden(X0,k3_tarski(X1)) )
    | ~ spl9_53 ),
    inference(avatar_component_clause,[],[f371])).

fof(f377,plain,
    ( spl9_54
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f349,f345,f154,f81,f375])).

fof(f154,plain,
    ( spl9_20
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f349,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | ~ spl9_6
    | ~ spl9_20
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f348,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f154])).

fof(f373,plain,
    ( spl9_53
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f117,f102,f93,f371])).

fof(f93,plain,
    ( spl9_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f102,plain,
    ( spl9_11
  <=> ! [X0,X2] :
        ( r2_hidden(sK7(X0,X2),X0)
        | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_tarski(X1))
        | ~ r1_tarski(X1,sK7(X1,X0)) )
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(resolution,[],[f103,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f103,plain,
    ( ! [X2,X0] :
        ( r2_hidden(sK7(X0,X2),X0)
        | ~ r2_hidden(X2,k3_tarski(X0)) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f353,plain,
    ( ~ spl9_51
    | ~ spl9_6
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f343,f340,f81,f351])).

fof(f340,plain,
    ( spl9_49
  <=> ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f343,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl9_6
    | ~ spl9_49 ),
    inference(resolution,[],[f341,f82])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f340])).

fof(f347,plain,
    ( spl9_50
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f223,f211,f77,f73,f69,f65,f61,f345])).

fof(f211,plain,
    ( spl9_29
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X3,X0,X1)
        | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f222,f62])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f221,f74])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f220,f70])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f219,f66])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | r2_hidden(X1,k4_orders_2(sK0,X0)) )
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(resolution,[],[f212,f78])).

fof(f212,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X3,X0,X1)
        | r2_hidden(X3,k4_orders_2(X0,X1)) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f211])).

fof(f342,plain,
    ( spl9_49
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f250,f243,f77,f73,f69,f65,f61,f340])).

fof(f243,plain,
    ( spl9_33
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f249,f62])).

fof(f249,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f248,f74])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f247,f70])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f246,f66])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl9_5
    | ~ spl9_33 ),
    inference(resolution,[],[f244,f78])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f243])).

fof(f268,plain,
    ( spl9_30
    | ~ spl9_7
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f230,f154,f85,f215])).

fof(f85,plain,
    ( spl9_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f230,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl9_7
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f86,f155])).

fof(f86,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f245,plain,
    ( spl9_33
    | ~ spl9_24
    | ~ spl9_27
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f241,f237,f192,f176,f243])).

fof(f176,plain,
    ( spl9_24
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v6_orders_2(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f192,plain,
    ( spl9_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f237,plain,
    ( spl9_32
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v6_orders_2(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl9_24
    | ~ spl9_27
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f240,f193])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f192])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f238,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( v6_orders_2(X2,X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f176])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v6_orders_2(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,(
    spl9_32 ),
    inference(avatar_split_clause,[],[f54,f237])).

fof(f54,plain,(
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
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

fof(f227,plain,
    ( spl9_31
    | ~ spl9_10
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f168,f157,f97,f225])).

fof(f157,plain,
    ( spl9_21
  <=> ! [X0] : ~ r2_hidden(X0,sK4(k4_orders_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f168,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ spl9_10
    | ~ spl9_21 ),
    inference(resolution,[],[f158,f98])).

fof(f158,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k4_orders_2(sK0,sK1)))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f213,plain,(
    spl9_29 ),
    inference(avatar_split_clause,[],[f56,f211])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f198,plain,(
    spl9_28 ),
    inference(avatar_split_clause,[],[f55,f196])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f194,plain,(
    spl9_27 ),
    inference(avatar_split_clause,[],[f45,f192])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f182,plain,
    ( spl9_25
    | ~ spl9_10
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f171,f157,f97,f180])).

fof(f171,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_10
    | ~ spl9_21 ),
    inference(backward_demodulation,[],[f158,f168])).

fof(f178,plain,(
    spl9_24 ),
    inference(avatar_split_clause,[],[f44,f176])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f163,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f46,f161])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(sK5(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f159,plain,
    ( spl9_20
    | spl9_21
    | ~ spl9_10
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f146,f138,f97,f157,f154])).

fof(f138,plain,
    ( spl9_18
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(k4_orders_2(sK0,sK1)))
        | k1_xboole_0 = k4_orders_2(sK0,sK1) )
    | ~ spl9_10
    | ~ spl9_18 ),
    inference(resolution,[],[f139,f98])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl9_18
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f132,f123,f93,f89,f138])).

fof(f123,plain,
    ( spl9_15
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f131,f90])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X1,X0)
        | ~ r1_tarski(k1_xboole_0,X1) )
    | ~ spl9_9
    | ~ spl9_15 ),
    inference(resolution,[],[f124,f94])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl9_15
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f121,f110,f85,f123])).

fof(f110,plain,
    ( spl9_13
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X3,X0)
        | r2_hidden(X2,k3_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(superposition,[],[f111,f86])).

fof(f111,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k3_tarski(X0))
        | ~ r2_hidden(X3,X0)
        | ~ r2_hidden(X2,X3) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f57,f110])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f104,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f58,f102])).

fof(f58,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f99,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f95,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f53,f93])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f91,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f31,f89])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f87,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f25,f85])).

fof(f25,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f83,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f24,f81])).

fof(f24,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (22272)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (22265)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (22272)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f534,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f104,f112,f125,f140,f159,f163,f178,f182,f194,f198,f213,f227,f239,f245,f268,f342,f347,f353,f373,f377,f380,f406,f493,f507])).
% 0.22/0.49  fof(f507,plain,(
% 0.22/0.49    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_22 | ~spl9_61),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f506])).
% 0.22/0.49  fof(f506,plain,(
% 0.22/0.49    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(subsumption_resolution,[],[f505,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl9_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f505,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(subsumption_resolution,[],[f504,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl9_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl9_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.49  fof(f504,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(subsumption_resolution,[],[f503,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    l1_orders_2(sK0) | ~spl9_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl9_5 <=> l1_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.49  fof(f503,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(subsumption_resolution,[],[f502,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    v5_orders_2(sK0) | ~spl9_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl9_4 <=> v5_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.49  fof(f502,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(subsumption_resolution,[],[f501,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v4_orders_2(sK0) | ~spl9_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl9_3 <=> v4_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.49  fof(f501,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(subsumption_resolution,[],[f495,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    v3_orders_2(sK0) | ~spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl9_2 <=> v3_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f495,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_22 | ~spl9_61)),
% 0.22/0.49    inference(resolution,[],[f492,f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m2_orders_2(sK5(X0,X1),X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl9_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  % (22273)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl9_22 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK5(X0,X1),X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.49  fof(f492,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1)) ) | ~spl9_61),
% 0.22/0.49    inference(avatar_component_clause,[],[f491])).
% 0.22/0.49  fof(f491,plain,(
% 0.22/0.49    spl9_61 <=> ! [X0] : ~m2_orders_2(X0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).
% 0.22/0.49  fof(f493,plain,(
% 0.22/0.49    spl9_61 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_10 | ~spl9_25 | ~spl9_28 | ~spl9_31 | ~spl9_50 | spl9_51),
% 0.22/0.49    inference(avatar_split_clause,[],[f453,f351,f345,f225,f196,f180,f97,f81,f77,f73,f69,f65,f61,f491])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl9_10 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    spl9_25 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    spl9_28 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    spl9_31 <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.49  fof(f345,plain,(
% 0.22/0.49    spl9_50 <=> ! [X1,X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 0.22/0.49  fof(f351,plain,(
% 0.22/0.49    spl9_51 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 0.22/0.49  fof(f453,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_10 | ~spl9_25 | ~spl9_28 | ~spl9_31 | ~spl9_50 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f449,f181])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl9_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f180])).
% 0.22/0.49  fof(f449,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~m2_orders_2(X0,sK0,sK1)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_10 | ~spl9_28 | ~spl9_31 | ~spl9_50 | spl9_51)),
% 0.22/0.49    inference(backward_demodulation,[],[f348,f444])).
% 0.22/0.49  fof(f444,plain,(
% 0.22/0.49    k1_xboole_0 = k4_orders_2(sK0,sK1) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_10 | ~spl9_28 | ~spl9_31 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f443,f366])).
% 0.22/0.49  fof(f366,plain,(
% 0.22/0.49    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_28 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f365,f62])).
% 0.22/0.49  fof(f365,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_28 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f364,f82])).
% 0.22/0.49  fof(f364,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_28 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f363,f78])).
% 0.22/0.49  fof(f363,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_28 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f362,f74])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl9_2 | ~spl9_3 | ~spl9_28 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f361,f70])).
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl9_2 | ~spl9_28 | spl9_51)),
% 0.22/0.49    inference(subsumption_resolution,[],[f360,f66])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl9_28 | spl9_51)),
% 0.22/0.49    inference(resolution,[],[f352,f197])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (m2_orders_2(X3,X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(X3,k4_orders_2(X0,X1))) ) | ~spl9_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f196])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ~m2_orders_2(k1_xboole_0,sK0,sK1) | spl9_51),
% 0.22/0.49    inference(avatar_component_clause,[],[f351])).
% 0.22/0.49  fof(f443,plain,(
% 0.22/0.49    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (~spl9_10 | ~spl9_31)),
% 0.22/0.49    inference(superposition,[],[f98,f226])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~spl9_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f225])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl9_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f348,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl9_6 | ~spl9_50)),
% 0.22/0.49    inference(resolution,[],[f346,f82])).
% 0.22/0.49  fof(f346,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) ) | ~spl9_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f345])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_22 | ~spl9_25 | ~spl9_54),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f405])).
% 0.22/0.49  fof(f405,plain,(
% 0.22/0.49    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f404,f62])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f403,f82])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f402,f78])).
% 0.22/0.49  fof(f402,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f401,f74])).
% 0.22/0.49  fof(f401,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f400,f70])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f399,f66])).
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_22 | ~spl9_25 | ~spl9_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f394,f181])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    r2_hidden(sK5(sK0,sK1),k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl9_22 | ~spl9_54)),
% 0.22/0.49    inference(resolution,[],[f376,f162])).
% 0.22/0.49  fof(f376,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k1_xboole_0)) ) | ~spl9_54),
% 0.22/0.49    inference(avatar_component_clause,[],[f375])).
% 0.22/0.49  fof(f375,plain,(
% 0.22/0.49    spl9_54 <=> ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~m2_orders_2(X0,sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 0.22/0.49  fof(f380,plain,(
% 0.22/0.49    spl9_25 | ~spl9_8 | ~spl9_30 | ~spl9_53),
% 0.22/0.49    inference(avatar_split_clause,[],[f379,f371,f215,f89,f180])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl9_8 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl9_30 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    spl9_53 <=> ! [X1,X0] : (~r2_hidden(X0,k3_tarski(X1)) | ~r1_tarski(X1,sK7(X1,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).
% 0.22/0.49  fof(f379,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl9_8 | ~spl9_30 | ~spl9_53)),
% 0.22/0.49    inference(forward_demodulation,[],[f378,f216])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl9_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f215])).
% 0.22/0.49  fof(f378,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k3_tarski(k1_xboole_0))) ) | (~spl9_8 | ~spl9_53)),
% 0.22/0.49    inference(resolution,[],[f372,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl9_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,sK7(X1,X0)) | ~r2_hidden(X0,k3_tarski(X1))) ) | ~spl9_53),
% 0.22/0.49    inference(avatar_component_clause,[],[f371])).
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    spl9_54 | ~spl9_6 | ~spl9_20 | ~spl9_50),
% 0.22/0.49    inference(avatar_split_clause,[],[f349,f345,f154,f81,f375])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl9_20 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.22/0.49  fof(f349,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~m2_orders_2(X0,sK0,sK1)) ) | (~spl9_6 | ~spl9_20 | ~spl9_50)),
% 0.22/0.49    inference(forward_demodulation,[],[f348,f155])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl9_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f154])).
% 0.22/0.49  fof(f373,plain,(
% 0.22/0.49    spl9_53 | ~spl9_9 | ~spl9_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f117,f102,f93,f371])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl9_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl9_11 <=> ! [X0,X2] : (r2_hidden(sK7(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k3_tarski(X1)) | ~r1_tarski(X1,sK7(X1,X0))) ) | (~spl9_9 | ~spl9_11)),
% 0.22/0.49    inference(resolution,[],[f103,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl9_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X2,X0] : (r2_hidden(sK7(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) ) | ~spl9_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f353,plain,(
% 0.22/0.49    ~spl9_51 | ~spl9_6 | ~spl9_49),
% 0.22/0.49    inference(avatar_split_clause,[],[f343,f340,f81,f351])).
% 0.22/0.49  fof(f340,plain,(
% 0.22/0.49    spl9_49 <=> ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.22/0.49  fof(f343,plain,(
% 0.22/0.49    ~m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl9_6 | ~spl9_49)),
% 0.22/0.49    inference(resolution,[],[f341,f82])).
% 0.22/0.49  fof(f341,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | ~spl9_49),
% 0.22/0.49    inference(avatar_component_clause,[],[f340])).
% 0.22/0.49  fof(f347,plain,(
% 0.22/0.49    spl9_50 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f223,f211,f77,f73,f69,f65,f61,f345])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    spl9_29 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f222,f62])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f221,f74])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f220,f70])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl9_2 | ~spl9_5 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f219,f66])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(X1,k4_orders_2(sK0,X0))) ) | (~spl9_5 | ~spl9_29)),
% 0.22/0.49    inference(resolution,[],[f212,f78])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) ) | ~spl9_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f211])).
% 0.22/0.49  fof(f342,plain,(
% 0.22/0.49    spl9_49 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_33),
% 0.22/0.49    inference(avatar_split_clause,[],[f250,f243,f77,f73,f69,f65,f61,f340])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    spl9_33 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f249,f62])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f248,f74])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f247,f70])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl9_2 | ~spl9_5 | ~spl9_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f246,f66])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl9_5 | ~spl9_33)),
% 0.22/0.49    inference(resolution,[],[f244,f78])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | ~spl9_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f243])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    spl9_30 | ~spl9_7 | ~spl9_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f230,f154,f85,f215])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl9_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0) | (~spl9_7 | ~spl9_20)),
% 0.22/0.49    inference(backward_demodulation,[],[f86,f155])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl9_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    spl9_33 | ~spl9_24 | ~spl9_27 | ~spl9_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f241,f237,f192,f176,f243])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl9_24 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl9_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    spl9_32 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl9_24 | ~spl9_27 | ~spl9_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f240,f193])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl9_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f192])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl9_24 | ~spl9_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f238,f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl9_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | ~spl9_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f237])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    spl9_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f54,f237])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl9_31 | ~spl9_10 | ~spl9_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f168,f157,f97,f225])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    spl9_21 <=> ! [X0] : ~r2_hidden(X0,sK4(k4_orders_2(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | (~spl9_10 | ~spl9_21)),
% 0.22/0.49    inference(resolution,[],[f158,f98])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK4(k4_orders_2(sK0,sK1)))) ) | ~spl9_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f157])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    spl9_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f56,f211])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl9_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f55,f196])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    spl9_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f192])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl9_25 | ~spl9_10 | ~spl9_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f171,f157,f97,f180])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl9_10 | ~spl9_21)),
% 0.22/0.49    inference(backward_demodulation,[],[f158,f168])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    spl9_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f176])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    spl9_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f161])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK5(X0,X1),X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl9_20 | spl9_21 | ~spl9_10 | ~spl9_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f146,f138,f97,f157,f154])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl9_18 <=> ! [X1,X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | ~r2_hidden(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK4(k4_orders_2(sK0,sK1))) | k1_xboole_0 = k4_orders_2(sK0,sK1)) ) | (~spl9_10 | ~spl9_18)),
% 0.22/0.49    inference(resolution,[],[f139,f98])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | ~r2_hidden(X1,X0)) ) | ~spl9_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    spl9_18 | ~spl9_8 | ~spl9_9 | ~spl9_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f123,f93,f89,f138])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl9_15 <=> ! [X1,X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k4_orders_2(sK0,sK1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | ~r2_hidden(X1,X0)) ) | (~spl9_8 | ~spl9_9 | ~spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f131,f90])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | ~r2_hidden(X1,X0) | ~r1_tarski(k1_xboole_0,X1)) ) | (~spl9_9 | ~spl9_15)),
% 0.22/0.49    inference(resolution,[],[f124,f94])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k4_orders_2(sK0,sK1)) | ~r2_hidden(X0,X1)) ) | ~spl9_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f123])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl9_15 | ~spl9_7 | ~spl9_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f121,f110,f85,f123])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl9_13 <=> ! [X3,X0,X2] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k4_orders_2(sK0,sK1)) | ~r2_hidden(X0,X1)) ) | (~spl9_7 | ~spl9_13)),
% 0.22/0.49    inference(superposition,[],[f111,f86])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (r2_hidden(X2,k3_tarski(X0)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) ) | ~spl9_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    spl9_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f57,f110])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl9_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f102])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0] : (r2_hidden(sK7(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl9_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f97])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl9_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f53,f93])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl9_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f89])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl9_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f85])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl9_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f81])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f77])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f73])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl9_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f69])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f65])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl9_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f61])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (22272)------------------------------
% 0.22/0.49  % (22272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22272)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (22272)Memory used [KB]: 10874
% 0.22/0.49  % (22272)Time elapsed: 0.033 s
% 0.22/0.49  % (22272)------------------------------
% 0.22/0.49  % (22272)------------------------------
% 0.22/0.50  % (22254)Success in time 0.132 s
%------------------------------------------------------------------------------
