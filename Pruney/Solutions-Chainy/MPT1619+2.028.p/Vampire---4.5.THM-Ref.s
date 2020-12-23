%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 214 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  406 ( 688 expanded)
%              Number of equality atoms :   46 (  92 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f73,f81,f85,f93,f97,f101,f114,f122,f150,f154,f163,f182,f201,f208,f228,f278,f414,f421])).

fof(f421,plain,
    ( ~ spl2_6
    | spl2_40 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl2_6
    | spl2_40 ),
    inference(unit_resulting_resolution,[],[f84,f308])).

fof(f308,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | spl2_40 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl2_40
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f84,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_6
  <=> ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f414,plain,
    ( ~ spl2_40
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f291,f275,f226,f206,f199,f152,f112,f99,f95,f79,f71,f306])).

fof(f71,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(sK1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f79,plain,
    ( spl2_5
  <=> ! [X0] : v1_funct_1(sK1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f95,plain,
    ( spl2_9
  <=> ! [X0] : v1_partfun1(sK1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f99,plain,
    ( spl2_10
  <=> ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f112,plain,
    ( spl2_13
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f152,plain,
    ( spl2_21
  <=> ! [X0] : v1_yellow_1(k7_funcop_1(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f199,plain,
    ( spl2_28
  <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f206,plain,
    ( spl2_29
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f226,plain,
    ( spl2_30
  <=> ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f275,plain,
    ( spl2_37
  <=> k1_xboole_0 = sK1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

% (18939)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (18940)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (18944)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (18954)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% (18941)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% (18938)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (18945)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (18947)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (18948)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f291,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f288,f284])).

fof(f284,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_37 ),
    inference(superposition,[],[f72,f277])).

fof(f277,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f275])).

fof(f72,plain,
    ( ! [X0] : v1_relat_1(sK1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f288,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f285,f282])).

fof(f282,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_37 ),
    inference(superposition,[],[f80,f277])).

fof(f80,plain,
    ( ! [X0] : v1_funct_1(sK1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f285,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f237,f280])).

fof(f280,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_37 ),
    inference(superposition,[],[f96,f277])).

fof(f96,plain,
    ( ! [X0] : v1_partfun1(sK1(X0),X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f237,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_21
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f224,f234])).

fof(f234,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl2_21
    | ~ spl2_30 ),
    inference(superposition,[],[f153,f227])).

fof(f227,plain,
    ( ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f153,plain,
    ( ! [X0] : v1_yellow_1(k7_funcop_1(X0,sK0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f152])).

fof(f224,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f223,f123])).

fof(f123,plain,
    ( ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f100,f113])).

fof(f113,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f100,plain,
    ( ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f223,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f222,f123])).

fof(f222,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f221,f123])).

fof(f221,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f220,f123])).

fof(f220,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f213,f123])).

fof(f213,plain,
    ( ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,sK0)
    | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,sK0))
    | ~ spl2_28
    | ~ spl2_29 ),
    inference(superposition,[],[f207,f200])).

fof(f200,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f199])).

fof(f207,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f206])).

fof(f278,plain,
    ( spl2_37
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f168,f161,f95,f91,f79,f71,f275])).

fof(f91,plain,
    ( spl2_8
  <=> ! [X0] : v4_relat_1(sK1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f161,plain,
    ( spl2_23
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f168,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f72,f80,f92,f96,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f92,plain,
    ( ! [X0] : v4_relat_1(sK1(X0),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f228,plain,
    ( spl2_30
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f123,f112,f99,f226])).

fof(f208,plain,
    ( spl2_29
    | spl2_2
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f187,f180,f66,f206])).

fof(f66,plain,
    ( spl2_2
  <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f180,plain,
    ( spl2_27
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f187,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | spl2_2
    | ~ spl2_27 ),
    inference(superposition,[],[f68,f181])).

fof(f181,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f180])).

fof(f68,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f201,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f159,f148,f61,f199])).

fof(f61,plain,
    ( spl2_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f148,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f159,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f63,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f63,plain,
    ( l1_orders_2(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f182,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f40,f180])).

fof(f40,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f163,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f41,f161])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

fof(f154,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f138,f120,f61,f152])).

fof(f120,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( v1_yellow_1(k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f138,plain,
    ( ! [X0] : v1_yellow_1(k7_funcop_1(X0,sK0))
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f63,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( v1_yellow_1(k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f150,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f52,f148])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f122,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f59,f120])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(forward_demodulation,[],[f51,f47])).

fof(f47,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f114,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f39,f112])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f101,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f58,f99])).

fof(f58,plain,(
    ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f36,f47])).

fof(f36,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f97,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    ! [X0] : v1_partfun1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_partfun1(sK1(X0),X0)
      & v1_funct_1(sK1(X0))
      & v4_relat_1(sK1(X0),X0)
      & v2_relat_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v2_relat_1(X1)
          & v1_relat_1(X1) )
     => ( v1_partfun1(sK1(X0),X0)
        & v1_funct_1(sK1(X0))
        & v4_relat_1(sK1(X0),X0)
        & v2_relat_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v2_relat_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_funcop_1)).

fof(f93,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    ! [X0] : v4_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(f81,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f64,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (18949)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.45  % (18949)Refutation not found, incomplete strategy% (18949)------------------------------
% 0.21/0.45  % (18949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (18949)Memory used [KB]: 10618
% 0.21/0.45  % (18949)Time elapsed: 0.004 s
% 0.21/0.45  % (18949)------------------------------
% 0.21/0.45  % (18949)------------------------------
% 0.21/0.47  % (18942)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18943)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (18950)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (18952)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (18943)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f424,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f64,f69,f73,f81,f85,f93,f97,f101,f114,f122,f150,f154,f163,f182,f201,f208,f228,f278,f414,f421])).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    ~spl2_6 | spl2_40),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f415])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    $false | (~spl2_6 | spl2_40)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f84,f308])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | spl2_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f306])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    spl2_40 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_6 <=> ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f414,plain,(
% 0.21/0.48    ~spl2_40 | ~spl2_3 | ~spl2_5 | ~spl2_9 | ~spl2_10 | ~spl2_13 | ~spl2_21 | ~spl2_28 | ~spl2_29 | ~spl2_30 | ~spl2_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f291,f275,f226,f206,f199,f152,f112,f99,f95,f79,f71,f306])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl2_3 <=> ! [X0] : v1_relat_1(sK1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl2_5 <=> ! [X0] : v1_funct_1(sK1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl2_9 <=> ! [X0] : v1_partfun1(sK1(X0),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl2_10 <=> ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl2_13 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl2_21 <=> ! [X0] : v1_yellow_1(k7_funcop_1(X0,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl2_28 <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl2_29 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    spl2_30 <=> ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    spl2_37 <=> k1_xboole_0 = sK1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.48  % (18939)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (18940)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (18944)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (18954)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (18941)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (18938)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (18945)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (18947)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (18948)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_5 | ~spl2_9 | ~spl2_10 | ~spl2_13 | ~spl2_21 | ~spl2_28 | ~spl2_29 | ~spl2_30 | ~spl2_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f288,f284])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | (~spl2_3 | ~spl2_37)),
% 0.21/0.49    inference(superposition,[],[f72,f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    k1_xboole_0 = sK1(k1_xboole_0) | ~spl2_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f275])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(sK1(X0))) ) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl2_5 | ~spl2_9 | ~spl2_10 | ~spl2_13 | ~spl2_21 | ~spl2_28 | ~spl2_29 | ~spl2_30 | ~spl2_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f285,f282])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    v1_funct_1(k1_xboole_0) | (~spl2_5 | ~spl2_37)),
% 0.21/0.49    inference(superposition,[],[f80,f277])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(sK1(X0))) ) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl2_9 | ~spl2_10 | ~spl2_13 | ~spl2_21 | ~spl2_28 | ~spl2_29 | ~spl2_30 | ~spl2_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f280])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl2_9 | ~spl2_37)),
% 0.21/0.49    inference(superposition,[],[f96,f277])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (v1_partfun1(sK1(X0),X0)) ) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl2_10 | ~spl2_13 | ~spl2_21 | ~spl2_28 | ~spl2_29 | ~spl2_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f234])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    v1_yellow_1(k1_xboole_0) | (~spl2_21 | ~spl2_30)),
% 0.21/0.49    inference(superposition,[],[f153,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) ) | ~spl2_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f226])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0] : (v1_yellow_1(k7_funcop_1(X0,sK0))) ) | ~spl2_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | (~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f223,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) ) | (~spl2_10 | ~spl2_13)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f100,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl2_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) ) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,sK0)) | (~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f222,f123])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,sK0)) | (~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f221,f123])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,sK0)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,sK0)) | (~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f220,f123])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,sK0)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,sK0)) | (~spl2_10 | ~spl2_13 | ~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f213,f123])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ~v1_yellow_1(k7_funcop_1(k1_xboole_0,sK0)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,sK0)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,sK0)) | (~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f212])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(k7_funcop_1(k1_xboole_0,sK0)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,sK0)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,sK0)) | (~spl2_28 | ~spl2_29)),
% 0.21/0.49    inference(superposition,[],[f207,f200])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))) ) | ~spl2_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f199])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl2_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f206])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl2_37 | ~spl2_3 | ~spl2_5 | ~spl2_8 | ~spl2_9 | ~spl2_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f161,f95,f91,f79,f71,f275])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl2_8 <=> ! [X0] : v4_relat_1(sK1(X0),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl2_23 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    k1_xboole_0 = sK1(k1_xboole_0) | (~spl2_3 | ~spl2_5 | ~spl2_8 | ~spl2_9 | ~spl2_23)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f72,f80,f92,f96,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl2_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) ) | ~spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    spl2_30 | ~spl2_10 | ~spl2_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f112,f99,f226])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl2_29 | spl2_2 | ~spl2_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f187,f180,f66,f206])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl2_2 <=> g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl2_27 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | (spl2_2 | ~spl2_27)),
% 0.21/0.49    inference(superposition,[],[f68,f181])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl2_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f180])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) | spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl2_28 | ~spl2_1 | ~spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f159,f148,f61,f199])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl2_1 <=> l1_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl2_20 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))) ) | (~spl2_1 | ~spl2_20)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl2_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    l1_orders_2(sK0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl2_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f180])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,axiom,(
% 0.21/0.49    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl2_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f161])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl2_21 | ~spl2_1 | ~spl2_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f120,f61,f152])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl2_15 <=> ! [X1,X0] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (v1_yellow_1(k7_funcop_1(X0,sK0))) ) | (~spl2_1 | ~spl2_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl2_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f148])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl2_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f120])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f51,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl2_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f112])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f99])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f36,f47])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f95])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (v1_partfun1(sK1(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v2_relat_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v2_relat_1(X1) & v1_relat_1(X1)) => (v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v2_relat_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0] : ? [X1] : (v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v2_relat_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_funcop_1)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl2_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f91])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f83])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f79])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f71])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f66])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f19])).
% 0.21/0.49  fof(f19,conjecture,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f61])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18943)------------------------------
% 0.21/0.49  % (18943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18943)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18943)Memory used [KB]: 6268
% 0.21/0.49  % (18943)Time elapsed: 0.067 s
% 0.21/0.49  % (18943)------------------------------
% 0.21/0.49  % (18943)------------------------------
% 0.21/0.49  % (18951)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (18937)Success in time 0.14 s
%------------------------------------------------------------------------------
