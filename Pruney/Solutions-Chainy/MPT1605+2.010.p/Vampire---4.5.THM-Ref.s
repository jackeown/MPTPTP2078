%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 350 expanded)
%              Number of leaves         :   48 ( 165 expanded)
%              Depth                    :    9
%              Number of atoms          :  885 (1409 expanded)
%              Number of equality atoms :   49 ( 105 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f90,f98,f102,f106,f110,f118,f122,f126,f146,f158,f166,f174,f185,f193,f197,f205,f210,f215,f222,f233,f259,f266,f277,f297,f306,f376,f402,f423,f440,f460,f492,f518])).

fof(f518,plain,
    ( spl4_3
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_67 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | spl4_3
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_67 ),
    inference(subsumption_resolution,[],[f516,f101])).

fof(f101,plain,
    ( ! [X0] : l1_orders_2(k2_yellow_1(X0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_9
  <=> ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f516,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_3
    | ~ spl4_14
    | ~ spl4_67 ),
    inference(subsumption_resolution,[],[f512,f77])).

fof(f77,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f512,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl4_14
    | ~ spl4_67 ),
    inference(superposition,[],[f121,f459])).

fof(f459,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl4_67
  <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f121,plain,
    ( ! [X0] :
        ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f492,plain,
    ( ~ spl4_42
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15
    | spl4_66 ),
    inference(avatar_split_clause,[],[f476,f455,f124,f104,f100,f253])).

fof(f253,plain,
    ( spl4_42
  <=> m1_subset_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f104,plain,
    ( spl4_10
  <=> ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f455,plain,
    ( spl4_66
  <=> r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f476,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15
    | spl4_66 ),
    inference(forward_demodulation,[],[f475,f105])).

fof(f105,plain,
    ( ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f475,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_9
    | ~ spl4_15
    | spl4_66 ),
    inference(subsumption_resolution,[],[f474,f101])).

fof(f474,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl4_15
    | spl4_66 ),
    inference(resolution,[],[f456,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(X0,k1_xboole_0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f456,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | spl4_66 ),
    inference(avatar_component_clause,[],[f455])).

fof(f460,plain,
    ( ~ spl4_66
    | ~ spl4_42
    | spl4_67
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f442,f438,f80,f458,f253,f455])).

fof(f80,plain,
    ( spl4_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f438,plain,
    ( spl4_64
  <=> ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f442,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(resolution,[],[f439,f81])).

fof(f81,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f439,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0) )
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f438])).

fof(f440,plain,
    ( spl4_64
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f426,f421,f400,f438])).

fof(f400,plain,
    ( spl4_58
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f421,plain,
    ( spl4_62
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3
        | r1_orders_2(k2_yellow_1(sK0),X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | ~ m1_subset_1(X4,sK0)
        | ~ r1_tarski(X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0)) )
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(duplicate_literal_removal,[],[f424])).

% (8175)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (8168)Refutation not found, incomplete strategy% (8168)------------------------------
% (8168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8168)Termination reason: Refutation not found, incomplete strategy

% (8168)Memory used [KB]: 10618
% (8168)Time elapsed: 0.089 s
% (8168)------------------------------
% (8168)------------------------------
% (8174)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (8169)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (8172)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (8160)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (8172)Refutation not found, incomplete strategy% (8172)------------------------------
% (8172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8172)Termination reason: Refutation not found, incomplete strategy

% (8172)Memory used [KB]: 6140
% (8172)Time elapsed: 0.094 s
% (8172)------------------------------
% (8172)------------------------------
% (8177)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (8176)Refutation not found, incomplete strategy% (8176)------------------------------
% (8176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8176)Termination reason: Refutation not found, incomplete strategy

% (8176)Memory used [KB]: 6140
% (8176)Time elapsed: 0.103 s
% (8176)------------------------------
% (8176)------------------------------
% (8160)Refutation not found, incomplete strategy% (8160)------------------------------
% (8160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8160)Termination reason: Refutation not found, incomplete strategy

% (8160)Memory used [KB]: 10618
% (8160)Time elapsed: 0.101 s
% (8160)------------------------------
% (8160)------------------------------
% (8177)Refutation not found, incomplete strategy% (8177)------------------------------
% (8177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8177)Termination reason: Refutation not found, incomplete strategy

% (8177)Memory used [KB]: 10618
% (8177)Time elapsed: 0.107 s
% (8177)------------------------------
% (8177)------------------------------
% (8163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (8167)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (8167)Refutation not found, incomplete strategy% (8167)------------------------------
% (8167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8167)Termination reason: Refutation not found, incomplete strategy

% (8167)Memory used [KB]: 6140
% (8167)Time elapsed: 0.100 s
% (8167)------------------------------
% (8167)------------------------------
% (8173)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f424,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0)
        | ~ m1_subset_1(X0,sK0)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0 )
    | ~ spl4_58
    | ~ spl4_62 ),
    inference(resolution,[],[f422,f401])).

fof(f401,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | ~ m1_subset_1(X3,sK0)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f400])).

fof(f422,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(k2_yellow_1(sK0),X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X4,sK0)
        | ~ r1_tarski(X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) )
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f421])).

fof(f423,plain,
    ( spl4_62
    | ~ spl4_36
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f378,f374,f220,f421])).

fof(f220,plain,
    ( spl4_36
  <=> ! [X1,X0] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f374,plain,
    ( spl4_53
  <=> ! [X1] :
        ( m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f378,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3
        | r1_orders_2(k2_yellow_1(sK0),X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | ~ m1_subset_1(X4,sK0)
        | ~ r1_tarski(X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) )
    | ~ spl4_36
    | ~ spl4_53 ),
    inference(resolution,[],[f375,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f220])).

fof(f375,plain,
    ( ! [X1] :
        ( m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1 )
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f374])).

fof(f402,plain,
    ( spl4_58
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_31
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f336,f304,f195,f104,f100,f400])).

fof(f195,plain,
    ( spl4_31
  <=> ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_yellow_0(X0,X1)
        | ~ r2_lattice3(X0,X1,X2)
        | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        | k1_yellow_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f304,plain,
    ( spl4_48
  <=> r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f336,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_31
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f335,f105])).

fof(f335,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 )
    | ~ spl4_9
    | ~ spl4_31
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f322,f101])).

fof(f322,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 )
    | ~ spl4_31
    | ~ spl4_48 ),
    inference(resolution,[],[f305,f196])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_yellow_0(X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ r2_lattice3(X0,X1,X2)
        | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        | k1_yellow_0(X0,X1) = X2 )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f195])).

fof(f305,plain,
    ( r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f304])).

fof(f376,plain,
    ( spl4_53
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_28
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f332,f304,f183,f104,f100,f374])).

fof(f183,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_yellow_0(X0,X1)
        | ~ r2_lattice3(X0,X1,X2)
        | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
        | k1_yellow_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f332,plain,
    ( ! [X1] :
        ( m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1)
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1 )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_28
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f331,f105])).

fof(f331,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1)
        | m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1 )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_28
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f330,f105])).

fof(f330,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1)
        | m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1 )
    | ~ spl4_9
    | ~ spl4_28
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f320,f101])).

fof(f320,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1)
        | m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1 )
    | ~ spl4_28
    | ~ spl4_48 ),
    inference(resolution,[],[f305,f184])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_yellow_0(X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ r2_lattice3(X0,X1,X2)
        | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
        | k1_yellow_0(X0,X1) = X2 )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f183])).

fof(f306,plain,
    ( spl4_48
    | ~ spl4_42
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f302,f295,f124,f104,f100,f253,f304])).

fof(f295,plain,
    ( spl4_47
  <=> ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f302,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f301,f105])).

fof(f301,plain,
    ( r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f300,f101])).

fof(f300,plain,
    ( r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl4_15
    | ~ spl4_47 ),
    inference(resolution,[],[f296,f125])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0) )
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( spl4_47
    | ~ spl4_42
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f284,f275,f164,f104,f100,f96,f253,f295])).

fof(f96,plain,
    ( spl4_8
  <=> ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f164,plain,
    ( spl4_25
  <=> ! [X1,X0,X2] :
        ( ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        | r1_yellow_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f275,plain,
    ( spl4_45
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0) )
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,sK0) )
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f282,f105])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f281,f97])).

fof(f97,plain,
    ( ! [X0] : v5_orders_2(k2_yellow_1(X0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_9
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f280,f101])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,sK0)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_yellow_0(k2_yellow_1(sK0),X0) )
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(resolution,[],[f276,f165])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ v5_orders_2(X0)
        | r1_yellow_0(X0,X1) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f164])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1))
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( spl4_45
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f261,f257,f80,f72,f275])).

fof(f72,plain,
    ( spl4_2
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f257,plain,
    ( spl4_43
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,sK3(k2_yellow_1(sK0),X1,X2))
        | ~ r1_tarski(X0,sK3(k2_yellow_1(sK0),X1,X2))
        | ~ m1_subset_1(X2,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X2)
        | r1_yellow_0(k2_yellow_1(sK0),X1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1)) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f260,f81])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | r1_yellow_0(k2_yellow_1(sK0),X0)
        | r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1)) )
    | ~ spl4_2
    | ~ spl4_43 ),
    inference(resolution,[],[f258,f73])).

fof(f73,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f258,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r1_tarski(X0,sK3(k2_yellow_1(sK0),X1,X2))
        | ~ m1_subset_1(X2,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X2)
        | r1_yellow_0(k2_yellow_1(sK0),X1)
        | r1_orders_2(k2_yellow_1(sK0),X0,sK3(k2_yellow_1(sK0),X1,X2)) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f257])).

fof(f266,plain,
    ( ~ spl4_2
    | ~ spl4_13
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_13
    | spl4_42 ),
    inference(subsumption_resolution,[],[f263,f73])).

fof(f263,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | ~ spl4_13
    | spl4_42 ),
    inference(resolution,[],[f254,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f254,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f253])).

fof(f259,plain,
    ( spl4_43
    | ~ spl4_13
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f234,f231,f116,f257])).

fof(f231,plain,
    ( spl4_38
  <=> ! [X3,X2,X4] :
        ( r1_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X4,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X3,X4)
        | r1_yellow_0(k2_yellow_1(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,sK3(k2_yellow_1(sK0),X1,X2))
        | ~ r1_tarski(X0,sK3(k2_yellow_1(sK0),X1,X2))
        | ~ m1_subset_1(X2,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X2)
        | r1_yellow_0(k2_yellow_1(sK0),X1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_13
    | ~ spl4_38 ),
    inference(resolution,[],[f232,f117])).

fof(f232,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X3,X4))
        | ~ r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X4,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X3,X4)
        | r1_yellow_0(k2_yellow_1(sK0),X3) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl4_38
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f224,f220,f191,f231])).

fof(f191,plain,
    ( spl4_30
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X2,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | r1_yellow_0(k2_yellow_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f224,plain,
    ( ! [X4,X2,X3] :
        ( r1_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X4,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X3,X4)
        | r1_yellow_0(k2_yellow_1(sK0),X3) )
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(resolution,[],[f221,f192])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X2,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | r1_yellow_0(k2_yellow_1(X0),X1) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f191])).

fof(f222,plain,
    ( spl4_36
    | spl4_1
    | ~ spl4_20
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f218,f213,f144,f68,f220])).

fof(f68,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X1,X2)
        | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f213,plain,
    ( spl4_35
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,X1) )
    | spl4_1
    | ~ spl4_20
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f217,f69])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_20
    | ~ spl4_35 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_20
    | ~ spl4_35 ),
    inference(resolution,[],[f214,f145])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( r3_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f144])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X1,X0)
        | r1_orders_2(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( spl4_35
    | spl4_1
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f211,f208,f68,f213])).

fof(f208,plain,
    ( spl4_34
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,X1)
        | ~ m1_subset_1(X2,X1)
        | r1_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ r3_orders_2(k2_yellow_1(X1),X0,X2)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X1,sK0) )
    | spl4_1
    | ~ spl4_34 ),
    inference(resolution,[],[f209,f69])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,X1)
        | r1_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ r3_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( spl4_34
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f206,f203,f108,f208])).

fof(f108,plain,
    ( spl4_11
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f203,plain,
    ( spl4_33
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v2_struct_0(k2_yellow_1(X0))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ m1_subset_1(X2,X1)
        | r1_orders_2(k2_yellow_1(X1),X0,X2)
        | ~ r3_orders_2(k2_yellow_1(X1),X0,X2)
        | v1_xboole_0(X1) )
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(resolution,[],[f204,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(k2_yellow_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,X0)
        | ~ m1_subset_1(X2,X0)
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f203])).

fof(f205,plain,
    ( spl4_33
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f181,f172,f104,f100,f88,f203])).

fof(f88,plain,
    ( spl4_6
  <=> ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f172,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v2_struct_0(k2_yellow_1(X0))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f180,f105])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f179,f105])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f178,f89])).

fof(f89,plain,
    ( ! [X0] : v3_orders_2(k2_yellow_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(k2_yellow_1(X0))
        | v2_struct_0(k2_yellow_1(X0))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
        | r1_orders_2(k2_yellow_1(X0),X1,X2)
        | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(resolution,[],[f173,f101])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f172])).

fof(f197,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f49,f195])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f193,plain,
    ( spl4_30
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f177,f156,f104,f100,f96,f191])).

fof(f156,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X1,X2)
        | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
        | r1_yellow_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X2,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | r1_yellow_0(k2_yellow_1(X0),X1) )
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f176,f97])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
        | ~ m1_subset_1(X2,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | ~ v5_orders_2(k2_yellow_1(X0))
        | r1_yellow_0(k2_yellow_1(X0),X1) )
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f175,f101])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
        | ~ l1_orders_2(k2_yellow_1(X0))
        | ~ m1_subset_1(X2,X0)
        | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
        | ~ v5_orders_2(k2_yellow_1(X0))
        | r1_yellow_0(k2_yellow_1(X0),X1) )
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(superposition,[],[f157,f105])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ v5_orders_2(X0)
        | r1_yellow_0(X0,X1) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f156])).

fof(f185,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f47,f183])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f174,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f60,f172])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f166,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f54,f164])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f158,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f52,f156])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f146,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f66,f144])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f65,f38])).

fof(f38,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f126,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f45,f124])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f122,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f44,f120])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f118,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f58,f116])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f110,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f106,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f38,f104])).

fof(f102,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f37,f100])).

fof(f37,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f98,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f96])).

fof(f35,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f74,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (8162)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.44  % (8170)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.44  % (8170)Refutation not found, incomplete strategy% (8170)------------------------------
% 0.21/0.44  % (8170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8170)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (8170)Memory used [KB]: 1663
% 0.21/0.44  % (8170)Time elapsed: 0.047 s
% 0.21/0.44  % (8170)------------------------------
% 0.21/0.44  % (8170)------------------------------
% 0.21/0.49  % (8158)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8158)Refutation not found, incomplete strategy% (8158)------------------------------
% 0.21/0.49  % (8158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8158)Memory used [KB]: 10618
% 0.21/0.49  % (8158)Time elapsed: 0.070 s
% 0.21/0.49  % (8158)------------------------------
% 0.21/0.49  % (8158)------------------------------
% 0.21/0.49  % (8166)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (8161)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (8165)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (8161)Refutation not found, incomplete strategy% (8161)------------------------------
% 0.21/0.50  % (8161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8161)Memory used [KB]: 1663
% 0.21/0.50  % (8161)Time elapsed: 0.085 s
% 0.21/0.50  % (8161)------------------------------
% 0.21/0.50  % (8161)------------------------------
% 0.21/0.50  % (8159)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (8171)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (8164)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (8157)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (8157)Refutation not found, incomplete strategy% (8157)------------------------------
% 0.21/0.50  % (8157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8157)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8157)Memory used [KB]: 6140
% 0.21/0.50  % (8157)Time elapsed: 0.090 s
% 0.21/0.50  % (8157)------------------------------
% 0.21/0.50  % (8157)------------------------------
% 0.21/0.50  % (8176)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (8166)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (8168)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f519,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f90,f98,f102,f106,f110,f118,f122,f126,f146,f158,f166,f174,f185,f193,f197,f205,f210,f215,f222,f233,f259,f266,f277,f297,f306,f376,f402,f423,f440,f460,f492,f518])).
% 0.21/0.51  fof(f518,plain,(
% 0.21/0.51    spl4_3 | ~spl4_9 | ~spl4_14 | ~spl4_67),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f517])).
% 0.21/0.51  fof(f517,plain,(
% 0.21/0.51    $false | (spl4_3 | ~spl4_9 | ~spl4_14 | ~spl4_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f516,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) ) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl4_9 <=> ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f516,plain,(
% 0.21/0.51    ~l1_orders_2(k2_yellow_1(sK0)) | (spl4_3 | ~spl4_14 | ~spl4_67)),
% 0.21/0.51    inference(subsumption_resolution,[],[f512,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) | spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl4_3 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f512,plain,(
% 0.21/0.51    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | (~spl4_14 | ~spl4_67)),
% 0.21/0.51    inference(superposition,[],[f121,f459])).
% 0.21/0.51  fof(f459,plain,(
% 0.21/0.51    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~spl4_67),
% 0.21/0.51    inference(avatar_component_clause,[],[f458])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    spl4_67 <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) ) | ~spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl4_14 <=> ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    ~spl4_42 | ~spl4_9 | ~spl4_10 | ~spl4_15 | spl4_66),
% 0.21/0.51    inference(avatar_split_clause,[],[f476,f455,f124,f104,f100,f253])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl4_42 <=> m1_subset_1(k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl4_10 <=> ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl4_15 <=> ! [X1,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_lattice3(X0,k1_xboole_0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.51  fof(f455,plain,(
% 0.21/0.51    spl4_66 <=> r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.21/0.51  fof(f476,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,sK0) | (~spl4_9 | ~spl4_10 | ~spl4_15 | spl4_66)),
% 0.21/0.51    inference(forward_demodulation,[],[f475,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) ) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f475,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_9 | ~spl4_15 | spl4_66)),
% 0.21/0.51    inference(subsumption_resolution,[],[f474,f101])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | (~spl4_15 | spl4_66)),
% 0.21/0.51    inference(resolution,[],[f456,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) ) | ~spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | spl4_66),
% 0.21/0.51    inference(avatar_component_clause,[],[f455])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    ~spl4_66 | ~spl4_42 | spl4_67 | ~spl4_4 | ~spl4_64),
% 0.21/0.51    inference(avatar_split_clause,[],[f442,f438,f80,f458,f253,f455])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl4_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f438,plain,(
% 0.21/0.51    spl4_64 <=> ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0 | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_64)),
% 0.21/0.51    inference(resolution,[],[f439,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0)) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0 | ~m1_subset_1(X0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0)) ) | ~spl4_64),
% 0.21/0.51    inference(avatar_component_clause,[],[f438])).
% 0.21/0.51  fof(f440,plain,(
% 0.21/0.51    spl4_64 | ~spl4_58 | ~spl4_62),
% 0.21/0.51    inference(avatar_split_clause,[],[f426,f421,f400,f438])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    spl4_58 <=> ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | ~r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    spl4_62 <=> ! [X3,X4] : (~m1_subset_1(X3,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 | r1_orders_2(k2_yellow_1(sK0),X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | ~m1_subset_1(X4,sK0) | ~r1_tarski(X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0 | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0))) ) | (~spl4_58 | ~spl4_62)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f424])).
% 0.21/0.51  % (8175)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (8168)Refutation not found, incomplete strategy% (8168)------------------------------
% 0.21/0.51  % (8168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8168)Memory used [KB]: 10618
% 0.21/0.51  % (8168)Time elapsed: 0.089 s
% 0.21/0.51  % (8168)------------------------------
% 0.21/0.51  % (8168)------------------------------
% 0.21/0.51  % (8174)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (8169)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8172)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (8160)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (8172)Refutation not found, incomplete strategy% (8172)------------------------------
% 0.21/0.51  % (8172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8172)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8172)Memory used [KB]: 6140
% 0.21/0.51  % (8172)Time elapsed: 0.094 s
% 0.21/0.51  % (8172)------------------------------
% 0.21/0.51  % (8172)------------------------------
% 0.21/0.51  % (8177)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (8176)Refutation not found, incomplete strategy% (8176)------------------------------
% 0.21/0.52  % (8176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8176)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8176)Memory used [KB]: 6140
% 0.21/0.52  % (8176)Time elapsed: 0.103 s
% 0.21/0.52  % (8176)------------------------------
% 0.21/0.52  % (8176)------------------------------
% 0.21/0.52  % (8160)Refutation not found, incomplete strategy% (8160)------------------------------
% 0.21/0.52  % (8160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8160)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8160)Memory used [KB]: 10618
% 0.21/0.52  % (8160)Time elapsed: 0.101 s
% 0.21/0.52  % (8160)------------------------------
% 0.21/0.52  % (8160)------------------------------
% 0.21/0.52  % (8177)Refutation not found, incomplete strategy% (8177)------------------------------
% 0.21/0.52  % (8177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8177)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8177)Memory used [KB]: 10618
% 0.21/0.52  % (8177)Time elapsed: 0.107 s
% 0.21/0.52  % (8177)------------------------------
% 0.21/0.52  % (8177)------------------------------
% 0.21/0.52  % (8163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (8167)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (8167)Refutation not found, incomplete strategy% (8167)------------------------------
% 0.21/0.52  % (8167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8167)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8167)Memory used [KB]: 6140
% 0.21/0.52  % (8167)Time elapsed: 0.100 s
% 0.21/0.52  % (8167)------------------------------
% 0.21/0.52  % (8167)------------------------------
% 0.21/0.52  % (8173)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  fof(f424,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0 | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,X0)) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X0) | ~m1_subset_1(X0,sK0) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X0) ) | (~spl4_58 | ~spl4_62)),
% 0.21/0.52    inference(resolution,[],[f422,f401])).
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    ( ! [X3] : (~r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | ~m1_subset_1(X3,sK0) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3) ) | ~spl4_58),
% 0.21/0.52    inference(avatar_component_clause,[],[f400])).
% 0.21/0.52  fof(f422,plain,(
% 0.21/0.52    ( ! [X4,X3] : (r1_orders_2(k2_yellow_1(sK0),X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X4,sK0) | ~r1_tarski(X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))) ) | ~spl4_62),
% 0.21/0.52    inference(avatar_component_clause,[],[f421])).
% 0.21/0.52  fof(f423,plain,(
% 0.21/0.52    spl4_62 | ~spl4_36 | ~spl4_53),
% 0.21/0.52    inference(avatar_split_clause,[],[f378,f374,f220,f421])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    spl4_36 <=> ! [X1,X0] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    spl4_53 <=> ! [X1] : (m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),sK0) | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    ( ! [X4,X3] : (~m1_subset_1(X3,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3 | r1_orders_2(k2_yellow_1(sK0),X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | ~m1_subset_1(X4,sK0) | ~r1_tarski(X4,sK1(k2_yellow_1(sK0),k1_xboole_0,X3))) ) | (~spl4_36 | ~spl4_53)),
% 0.21/0.52    inference(resolution,[],[f375,f221])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,X1)) ) | ~spl4_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f220])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),sK0) | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1) ) | ~spl4_53),
% 0.21/0.52    inference(avatar_component_clause,[],[f374])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    spl4_58 | ~spl4_9 | ~spl4_10 | ~spl4_31 | ~spl4_48),
% 0.21/0.52    inference(avatar_split_clause,[],[f336,f304,f195,f104,f100,f400])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl4_31 <=> ! [X1,X0,X2] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    spl4_48 <=> r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | ~r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3) ) | (~spl4_9 | ~spl4_10 | ~spl4_31 | ~spl4_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f335,f105])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | ~r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3) ) | (~spl4_9 | ~spl4_31 | ~spl4_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f322,f101])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X3) | ~r1_orders_2(k2_yellow_1(sK0),X3,sK1(k2_yellow_1(sK0),k1_xboole_0,X3)) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X3) ) | (~spl4_31 | ~spl4_48)),
% 0.21/0.52    inference(resolution,[],[f305,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2) ) | ~spl4_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f195])).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~spl4_48),
% 0.21/0.52    inference(avatar_component_clause,[],[f304])).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    spl4_53 | ~spl4_9 | ~spl4_10 | ~spl4_28 | ~spl4_48),
% 0.21/0.52    inference(avatar_split_clause,[],[f332,f304,f183,f104,f100,f374])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl4_28 <=> ! [X1,X0,X2] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),sK0) | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1) ) | (~spl4_9 | ~spl4_10 | ~spl4_28 | ~spl4_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f331,f105])).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1) | m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),u1_struct_0(k2_yellow_1(sK0))) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1) ) | (~spl4_9 | ~spl4_10 | ~spl4_28 | ~spl4_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f330,f105])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1) | m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),u1_struct_0(k2_yellow_1(sK0))) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1) ) | (~spl4_9 | ~spl4_28 | ~spl4_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f320,f101])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,X1) | m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,X1),u1_struct_0(k2_yellow_1(sK0))) | k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) = X1) ) | (~spl4_28 | ~spl4_48)),
% 0.21/0.52    inference(resolution,[],[f305,f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2) ) | ~spl4_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    spl4_48 | ~spl4_42 | ~spl4_9 | ~spl4_10 | ~spl4_15 | ~spl4_47),
% 0.21/0.52    inference(avatar_split_clause,[],[f302,f295,f124,f104,f100,f253,f304])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    spl4_47 <=> ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.52  fof(f302,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,sK0) | r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | (~spl4_9 | ~spl4_10 | ~spl4_15 | ~spl4_47)),
% 0.21/0.52    inference(forward_demodulation,[],[f301,f105])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_9 | ~spl4_15 | ~spl4_47)),
% 0.21/0.52    inference(subsumption_resolution,[],[f300,f101])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    r1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | (~spl4_15 | ~spl4_47)),
% 0.21/0.52    inference(resolution,[],[f296,f125])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0)) ) | ~spl4_47),
% 0.21/0.52    inference(avatar_component_clause,[],[f295])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    spl4_47 | ~spl4_42 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_25 | ~spl4_45),
% 0.21/0.52    inference(avatar_split_clause,[],[f284,f275,f164,f104,f100,f96,f253,f295])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_8 <=> ! [X0] : v5_orders_2(k2_yellow_1(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl4_25 <=> ! [X1,X0,X2] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_yellow_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    spl4_45 <=> ! [X1,X0] : (~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | r1_yellow_0(k2_yellow_1(sK0),X0) | r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0)) ) | (~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_25 | ~spl4_45)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f283])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(k1_xboole_0,sK0)) ) | (~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_25 | ~spl4_45)),
% 0.21/0.52    inference(forward_demodulation,[],[f282,f105])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_8 | ~spl4_9 | ~spl4_25 | ~spl4_45)),
% 0.21/0.52    inference(subsumption_resolution,[],[f281,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) ) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_9 | ~spl4_25 | ~spl4_45)),
% 0.21/0.52    inference(subsumption_resolution,[],[f280,f101])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(k1_xboole_0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_25 | ~spl4_45)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f278])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | r1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(k1_xboole_0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_yellow_0(k2_yellow_1(sK0),X0)) ) | (~spl4_25 | ~spl4_45)),
% 0.21/0.52    inference(resolution,[],[f276,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~v5_orders_2(X0) | r1_yellow_0(X0,X1)) ) | ~spl4_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f164])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1)) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | r1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_45),
% 0.21/0.52    inference(avatar_component_clause,[],[f275])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    spl4_45 | ~spl4_2 | ~spl4_4 | ~spl4_43),
% 0.21/0.52    inference(avatar_split_clause,[],[f261,f257,f80,f72,f275])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl4_2 <=> r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    spl4_43 <=> ! [X1,X0,X2] : (r1_orders_2(k2_yellow_1(sK0),X0,sK3(k2_yellow_1(sK0),X1,X2)) | ~r1_tarski(X0,sK3(k2_yellow_1(sK0),X1,X2)) | ~m1_subset_1(X2,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X1,X2) | r1_yellow_0(k2_yellow_1(sK0),X1) | ~r2_hidden(X0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | r1_yellow_0(k2_yellow_1(sK0),X0) | r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1))) ) | (~spl4_2 | ~spl4_4 | ~spl4_43)),
% 0.21/0.52    inference(subsumption_resolution,[],[f260,f81])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | r1_yellow_0(k2_yellow_1(sK0),X0) | r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,sK3(k2_yellow_1(sK0),X0,X1))) ) | (~spl4_2 | ~spl4_43)),
% 0.21/0.52    inference(resolution,[],[f258,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    r2_hidden(k1_xboole_0,sK0) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | ~r1_tarski(X0,sK3(k2_yellow_1(sK0),X1,X2)) | ~m1_subset_1(X2,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X1,X2) | r1_yellow_0(k2_yellow_1(sK0),X1) | r1_orders_2(k2_yellow_1(sK0),X0,sK3(k2_yellow_1(sK0),X1,X2))) ) | ~spl4_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f257])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    ~spl4_2 | ~spl4_13 | spl4_42),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f265])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    $false | (~spl4_2 | ~spl4_13 | spl4_42)),
% 0.21/0.52    inference(subsumption_resolution,[],[f263,f73])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ~r2_hidden(k1_xboole_0,sK0) | (~spl4_13 | spl4_42)),
% 0.21/0.52    inference(resolution,[],[f254,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl4_13 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,sK0) | spl4_42),
% 0.21/0.52    inference(avatar_component_clause,[],[f253])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl4_43 | ~spl4_13 | ~spl4_38),
% 0.21/0.52    inference(avatar_split_clause,[],[f234,f231,f116,f257])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    spl4_38 <=> ! [X3,X2,X4] : (r1_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X2,sK0) | ~r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X4,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X3,X4) | r1_yellow_0(k2_yellow_1(sK0),X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,sK3(k2_yellow_1(sK0),X1,X2)) | ~r1_tarski(X0,sK3(k2_yellow_1(sK0),X1,X2)) | ~m1_subset_1(X2,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X1,X2) | r1_yellow_0(k2_yellow_1(sK0),X1) | ~r2_hidden(X0,sK0)) ) | (~spl4_13 | ~spl4_38)),
% 0.21/0.52    inference(resolution,[],[f232,f117])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (~m1_subset_1(X2,sK0) | r1_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X3,X4)) | ~r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X4,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X3,X4) | r1_yellow_0(k2_yellow_1(sK0),X3)) ) | ~spl4_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f231])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    spl4_38 | ~spl4_30 | ~spl4_36),
% 0.21/0.52    inference(avatar_split_clause,[],[f224,f220,f191,f231])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    spl4_30 <=> ! [X1,X0,X2] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_yellow_0(k2_yellow_1(X0),X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (r1_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X2,sK0) | ~r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X4,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X3,X4) | r1_yellow_0(k2_yellow_1(sK0),X3)) ) | (~spl4_30 | ~spl4_36)),
% 0.21/0.52    inference(resolution,[],[f221,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_yellow_0(k2_yellow_1(X0),X1)) ) | ~spl4_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f191])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    spl4_36 | spl4_1 | ~spl4_20 | ~spl4_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f218,f213,f144,f68,f220])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl4_1 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl4_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.33/0.52  fof(f213,plain,(
% 1.33/0.52    spl4_35 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),X1,X0) | ~r3_orders_2(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X1,sK0))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.33/0.52  fof(f218,plain,(
% 1.33/0.52    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,X1)) ) | (spl4_1 | ~spl4_20 | ~spl4_35)),
% 1.33/0.52    inference(subsumption_resolution,[],[f217,f69])).
% 1.33/0.52  fof(f69,plain,(
% 1.33/0.52    ~v1_xboole_0(sK0) | spl4_1),
% 1.33/0.52    inference(avatar_component_clause,[],[f68])).
% 1.33/0.52  fof(f217,plain,(
% 1.33/0.52    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0) | ~r1_tarski(X0,X1)) ) | (~spl4_20 | ~spl4_35)),
% 1.33/0.52    inference(duplicate_literal_removal,[],[f216])).
% 1.33/0.52  fof(f216,plain,(
% 1.33/0.52    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,sK0)) ) | (~spl4_20 | ~spl4_35)),
% 1.33/0.52    inference(resolution,[],[f214,f145])).
% 1.33/0.52  fof(f145,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) ) | ~spl4_20),
% 1.33/0.52    inference(avatar_component_clause,[],[f144])).
% 1.33/0.52  fof(f214,plain,(
% 1.33/0.52    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),X1,X0) | r1_orders_2(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl4_35),
% 1.33/0.52    inference(avatar_component_clause,[],[f213])).
% 1.33/0.52  fof(f215,plain,(
% 1.33/0.52    spl4_35 | spl4_1 | ~spl4_34),
% 1.33/0.52    inference(avatar_split_clause,[],[f211,f208,f68,f213])).
% 1.33/0.52  fof(f208,plain,(
% 1.33/0.52    spl4_34 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r3_orders_2(k2_yellow_1(X1),X0,X2) | v1_xboole_0(X1))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.33/0.52  fof(f211,plain,(
% 1.33/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),X1,X0) | ~r3_orders_2(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X1,sK0)) ) | (spl4_1 | ~spl4_34)),
% 1.33/0.52    inference(resolution,[],[f209,f69])).
% 1.33/0.52  fof(f209,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r3_orders_2(k2_yellow_1(X1),X0,X2) | ~m1_subset_1(X0,X1)) ) | ~spl4_34),
% 1.33/0.52    inference(avatar_component_clause,[],[f208])).
% 1.33/0.52  fof(f210,plain,(
% 1.33/0.52    spl4_34 | ~spl4_11 | ~spl4_33),
% 1.33/0.52    inference(avatar_split_clause,[],[f206,f203,f108,f208])).
% 1.33/0.52  fof(f108,plain,(
% 1.33/0.52    spl4_11 <=> ! [X0] : (v1_xboole_0(X0) | ~v2_struct_0(k2_yellow_1(X0)))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.33/0.52  fof(f203,plain,(
% 1.33/0.52    spl4_33 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.33/0.52  fof(f206,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r3_orders_2(k2_yellow_1(X1),X0,X2) | v1_xboole_0(X1)) ) | (~spl4_11 | ~spl4_33)),
% 1.33/0.52    inference(resolution,[],[f204,f109])).
% 1.33/0.52  fof(f109,plain,(
% 1.33/0.52    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) ) | ~spl4_11),
% 1.33/0.52    inference(avatar_component_clause,[],[f108])).
% 1.33/0.52  fof(f204,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | ~spl4_33),
% 1.33/0.52    inference(avatar_component_clause,[],[f203])).
% 1.33/0.52  fof(f205,plain,(
% 1.33/0.52    spl4_33 | ~spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_27),
% 1.33/0.52    inference(avatar_split_clause,[],[f181,f172,f104,f100,f88,f203])).
% 1.33/0.52  fof(f88,plain,(
% 1.33/0.52    spl4_6 <=> ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.33/0.52  fof(f172,plain,(
% 1.33/0.52    spl4_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.33/0.52  fof(f181,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_27)),
% 1.33/0.52    inference(forward_demodulation,[],[f180,f105])).
% 1.33/0.52  fof(f180,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_6 | ~spl4_9 | ~spl4_10 | ~spl4_27)),
% 1.33/0.52    inference(forward_demodulation,[],[f179,f105])).
% 1.33/0.52  fof(f179,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_6 | ~spl4_9 | ~spl4_27)),
% 1.33/0.52    inference(subsumption_resolution,[],[f178,f89])).
% 1.33/0.52  fof(f89,plain,(
% 1.33/0.52    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) ) | ~spl4_6),
% 1.33/0.52    inference(avatar_component_clause,[],[f88])).
% 1.33/0.52  fof(f178,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) ) | (~spl4_9 | ~spl4_27)),
% 1.33/0.52    inference(resolution,[],[f173,f101])).
% 1.33/0.52  fof(f173,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) ) | ~spl4_27),
% 1.33/0.52    inference(avatar_component_clause,[],[f172])).
% 1.33/0.52  fof(f197,plain,(
% 1.33/0.52    spl4_31),
% 1.33/0.52    inference(avatar_split_clause,[],[f49,f195])).
% 1.33/0.52  fof(f49,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2) )),
% 1.33/0.52    inference(cnf_transformation,[],[f22])).
% 1.33/0.52  fof(f22,plain,(
% 1.33/0.52    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.52    inference(flattening,[],[f21])).
% 1.33/0.52  fof(f21,plain,(
% 1.33/0.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.52    inference(ennf_transformation,[],[f5])).
% 1.33/0.52  fof(f5,axiom,(
% 1.33/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.33/0.52  fof(f193,plain,(
% 1.33/0.52    spl4_30 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_23),
% 1.33/0.52    inference(avatar_split_clause,[],[f177,f156,f104,f100,f96,f191])).
% 1.33/0.52  fof(f156,plain,(
% 1.33/0.52    spl4_23 <=> ! [X1,X0,X2] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1))),
% 1.33/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.33/0.52  fof(f177,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_yellow_0(k2_yellow_1(X0),X1)) ) | (~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_23)),
% 1.33/0.52    inference(subsumption_resolution,[],[f176,f97])).
% 1.33/0.52  fof(f176,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~v5_orders_2(k2_yellow_1(X0)) | r1_yellow_0(k2_yellow_1(X0),X1)) ) | (~spl4_9 | ~spl4_10 | ~spl4_23)),
% 1.33/0.52    inference(subsumption_resolution,[],[f175,f101])).
% 1.33/0.52  fof(f175,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~v5_orders_2(k2_yellow_1(X0)) | r1_yellow_0(k2_yellow_1(X0),X1)) ) | (~spl4_10 | ~spl4_23)),
% 1.33/0.52    inference(superposition,[],[f157,f105])).
% 1.33/0.52  fof(f157,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~v5_orders_2(X0) | r1_yellow_0(X0,X1)) ) | ~spl4_23),
% 1.33/0.52    inference(avatar_component_clause,[],[f156])).
% 1.33/0.52  fof(f185,plain,(
% 1.33/0.52    spl4_28),
% 1.33/0.52    inference(avatar_split_clause,[],[f47,f183])).
% 1.33/0.52  fof(f47,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2) )),
% 1.33/0.52    inference(cnf_transformation,[],[f22])).
% 1.33/0.52  fof(f174,plain,(
% 1.33/0.52    spl4_27),
% 1.33/0.52    inference(avatar_split_clause,[],[f60,f172])).
% 1.33/0.52  fof(f60,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f27])).
% 1.33/0.52  fof(f27,plain,(
% 1.33/0.52    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.52    inference(flattening,[],[f26])).
% 1.33/0.52  fof(f26,plain,(
% 1.33/0.52    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.33/0.52    inference(ennf_transformation,[],[f3])).
% 1.33/0.52  fof(f3,axiom,(
% 1.33/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.33/0.52  fof(f166,plain,(
% 1.33/0.52    spl4_25),
% 1.33/0.52    inference(avatar_split_clause,[],[f54,f164])).
% 1.33/0.52  fof(f54,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_yellow_0(X0,X1)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f24])).
% 1.33/0.52  fof(f24,plain,(
% 1.33/0.52    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.33/0.52    inference(flattening,[],[f23])).
% 1.33/0.52  fof(f23,plain,(
% 1.33/0.52    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.33/0.52    inference(ennf_transformation,[],[f6])).
% 1.33/0.52  fof(f6,axiom,(
% 1.33/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).
% 1.33/0.52  fof(f158,plain,(
% 1.33/0.52    spl4_23),
% 1.33/0.52    inference(avatar_split_clause,[],[f52,f156])).
% 1.33/0.52  fof(f52,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f24])).
% 1.33/0.52  fof(f146,plain,(
% 1.33/0.52    spl4_20),
% 1.33/0.52    inference(avatar_split_clause,[],[f66,f144])).
% 1.33/0.52  fof(f66,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 1.33/0.52    inference(forward_demodulation,[],[f65,f38])).
% 1.33/0.52  fof(f38,plain,(
% 1.33/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.33/0.52    inference(cnf_transformation,[],[f11])).
% 1.33/0.52  fof(f11,axiom,(
% 1.33/0.52    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.33/0.52  fof(f65,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 1.33/0.52    inference(forward_demodulation,[],[f42,f38])).
% 1.33/0.52  fof(f42,plain,(
% 1.33/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f18])).
% 1.33/0.52  fof(f18,plain,(
% 1.33/0.52    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.33/0.52    inference(ennf_transformation,[],[f12])).
% 1.33/0.52  fof(f12,axiom,(
% 1.33/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 1.33/0.52  fof(f126,plain,(
% 1.33/0.52    spl4_15),
% 1.33/0.52    inference(avatar_split_clause,[],[f45,f124])).
% 1.33/0.52  fof(f45,plain,(
% 1.33/0.52    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_lattice3(X0,k1_xboole_0,X1)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f20])).
% 1.33/0.52  fof(f20,plain,(
% 1.33/0.52    ! [X0] : (! [X1] : ((r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.52    inference(ennf_transformation,[],[f7])).
% 1.33/0.52  fof(f7,axiom,(
% 1.33/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 1.33/0.52  fof(f122,plain,(
% 1.33/0.52    spl4_14),
% 1.33/0.52    inference(avatar_split_clause,[],[f44,f120])).
% 1.33/0.52  fof(f44,plain,(
% 1.33/0.52    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f19])).
% 1.33/0.52  fof(f19,plain,(
% 1.33/0.52    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.33/0.52    inference(ennf_transformation,[],[f4])).
% 1.33/0.52  fof(f4,axiom,(
% 1.33/0.52    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.33/0.52  fof(f118,plain,(
% 1.33/0.52    spl4_13),
% 1.33/0.52    inference(avatar_split_clause,[],[f58,f116])).
% 1.33/0.52  fof(f58,plain,(
% 1.33/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f25])).
% 1.33/0.52  fof(f25,plain,(
% 1.33/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.33/0.52    inference(ennf_transformation,[],[f2])).
% 1.33/0.52  fof(f2,axiom,(
% 1.33/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.33/0.52  fof(f110,plain,(
% 1.33/0.52    spl4_11),
% 1.33/0.52    inference(avatar_split_clause,[],[f40,f108])).
% 1.33/0.52  fof(f40,plain,(
% 1.33/0.52    ( ! [X0] : (v1_xboole_0(X0) | ~v2_struct_0(k2_yellow_1(X0))) )),
% 1.33/0.52    inference(cnf_transformation,[],[f17])).
% 1.33/0.52  fof(f17,plain,(
% 1.33/0.52    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 1.33/0.52    inference(ennf_transformation,[],[f10])).
% 1.33/0.52  fof(f10,axiom,(
% 1.33/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 1.33/0.52  fof(f106,plain,(
% 1.33/0.52    spl4_10),
% 1.33/0.52    inference(avatar_split_clause,[],[f38,f104])).
% 1.33/0.52  fof(f102,plain,(
% 1.33/0.52    spl4_9),
% 1.33/0.52    inference(avatar_split_clause,[],[f37,f100])).
% 1.33/0.52  fof(f37,plain,(
% 1.33/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.33/0.52    inference(cnf_transformation,[],[f8])).
% 1.33/0.52  fof(f8,axiom,(
% 1.33/0.52    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.33/0.52  fof(f98,plain,(
% 1.33/0.52    spl4_8),
% 1.33/0.52    inference(avatar_split_clause,[],[f35,f96])).
% 1.33/0.52  fof(f35,plain,(
% 1.33/0.52    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 1.33/0.52    inference(cnf_transformation,[],[f9])).
% 1.33/0.52  fof(f9,axiom,(
% 1.33/0.52    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 1.33/0.52  fof(f90,plain,(
% 1.33/0.52    spl4_6),
% 1.33/0.52    inference(avatar_split_clause,[],[f33,f88])).
% 1.33/0.52  fof(f33,plain,(
% 1.33/0.52    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.33/0.52    inference(cnf_transformation,[],[f9])).
% 1.33/0.52  fof(f82,plain,(
% 1.33/0.52    spl4_4),
% 1.33/0.52    inference(avatar_split_clause,[],[f31,f80])).
% 1.33/0.52  fof(f31,plain,(
% 1.33/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.33/0.52    inference(cnf_transformation,[],[f1])).
% 1.33/0.52  fof(f1,axiom,(
% 1.33/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.33/0.52  fof(f78,plain,(
% 1.33/0.52    ~spl4_3),
% 1.33/0.52    inference(avatar_split_clause,[],[f30,f76])).
% 1.33/0.52  fof(f30,plain,(
% 1.33/0.52    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 1.33/0.52    inference(cnf_transformation,[],[f16])).
% 1.33/0.52  fof(f16,plain,(
% 1.33/0.52    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 1.33/0.52    inference(flattening,[],[f15])).
% 1.33/0.52  fof(f15,plain,(
% 1.33/0.52    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 1.33/0.52    inference(ennf_transformation,[],[f14])).
% 1.33/0.52  fof(f14,negated_conjecture,(
% 1.33/0.52    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.33/0.52    inference(negated_conjecture,[],[f13])).
% 1.33/0.52  fof(f13,conjecture,(
% 1.33/0.52    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.33/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 1.33/0.52  fof(f74,plain,(
% 1.33/0.52    spl4_2),
% 1.33/0.52    inference(avatar_split_clause,[],[f29,f72])).
% 1.33/0.52  fof(f29,plain,(
% 1.33/0.52    r2_hidden(k1_xboole_0,sK0)),
% 1.33/0.52    inference(cnf_transformation,[],[f16])).
% 1.33/0.52  fof(f70,plain,(
% 1.33/0.52    ~spl4_1),
% 1.33/0.52    inference(avatar_split_clause,[],[f28,f68])).
% 1.33/0.52  fof(f28,plain,(
% 1.33/0.52    ~v1_xboole_0(sK0)),
% 1.33/0.52    inference(cnf_transformation,[],[f16])).
% 1.33/0.52  % SZS output end Proof for theBenchmark
% 1.33/0.52  % (8166)------------------------------
% 1.33/0.52  % (8166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.52  % (8166)Termination reason: Refutation
% 1.33/0.52  
% 1.33/0.52  % (8166)Memory used [KB]: 10874
% 1.33/0.52  % (8166)Time elapsed: 0.085 s
% 1.33/0.52  % (8166)------------------------------
% 1.33/0.52  % (8166)------------------------------
% 1.33/0.52  % (8155)Success in time 0.152 s
%------------------------------------------------------------------------------
