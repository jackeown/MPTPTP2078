%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 117 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  220 ( 321 expanded)
%              Number of equality atoms :   35 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f76,f98,f102,f114,f128,f136,f149,f185,f222,f243])).

fof(f243,plain,
    ( ~ spl5_10
    | ~ spl5_14
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_14
    | spl5_30 ),
    inference(subsumption_resolution,[],[f221,f238])).

fof(f238,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f113,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f113,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_14
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f221,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl5_30
  <=> r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f222,plain,
    ( ~ spl5_30
    | ~ spl5_1
    | ~ spl5_18
    | spl5_25 ),
    inference(avatar_split_clause,[],[f186,f182,f134,f54,f219])).

% (22127)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f54,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f134,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f182,plain,
    ( spl5_25
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f186,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_18
    | spl5_25 ),
    inference(unit_resulting_resolution,[],[f56,f184,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f134])).

fof(f184,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f182])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f185,plain,
    ( ~ spl5_1
    | ~ spl5_25
    | spl5_3
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f165,f147,f125,f64,f182,f54])).

fof(f64,plain,
    ( spl5_3
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f125,plain,
    ( spl5_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f147,plain,
    ( spl5_20
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f165,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | spl5_3
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f161,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f161,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | spl5_3
    | ~ spl5_20 ),
    inference(superposition,[],[f66,f148])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f66,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f149,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f48,f147])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f136,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f44,f134])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f128,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f117,f100,f59,f125])).

fof(f59,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f117,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f61,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f61,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f114,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f81,f74,f69,f112])).

fof(f69,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f74,plain,
    ( spl5_5
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f71,f75])).

fof(f75,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f71,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f102,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

% (22138)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (22137)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (22135)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f98,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f76,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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

fof(f72,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f67,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:00:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (22129)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (22130)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (22126)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (22129)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f76,f98,f102,f114,f128,f136,f149,f185,f222,f243])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    ~spl5_10 | ~spl5_14 | spl5_30),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f242])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    $false | (~spl5_10 | ~spl5_14 | spl5_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f221,f238])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl5_10 | ~spl5_14)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f113,f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl5_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl5_10 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f112])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl5_14 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    ~r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) | spl5_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f219])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    spl5_30 <=> r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    ~spl5_30 | ~spl5_1 | ~spl5_18 | spl5_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f186,f182,f134,f54,f219])).
% 0.20/0.47  % (22127)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl5_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    spl5_18 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    spl5_25 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ~r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) | (~spl5_1 | ~spl5_18 | spl5_25)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f56,f184,f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl5_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f134])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | spl5_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f182])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_25 | spl5_3 | ~spl5_16 | ~spl5_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f165,f147,f125,f64,f182,f54])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl5_3 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl5_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    spl5_20 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(sK2) | (spl5_3 | ~spl5_16 | ~spl5_20)),
% 0.20/0.47    inference(forward_demodulation,[],[f161,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f125])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | ~v1_relat_1(sK2) | (spl5_3 | ~spl5_20)),
% 0.20/0.47    inference(superposition,[],[f66,f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) ) | ~spl5_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f147])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    spl5_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f147])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    spl5_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f134])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl5_16 | ~spl5_2 | ~spl5_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f117,f100,f59,f125])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl5_2 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl5_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl5_2 | ~spl5_11)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f61,f101])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl5_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f100])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl5_14 | ~spl5_4 | ~spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f81,f74,f69,f112])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl5_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl5_5 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f71,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl5_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f100])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  % (22138)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (22137)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (22135)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl5_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f96])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f74])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(rectify,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f69])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ~spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f64])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f14])).
% 0.20/0.48  fof(f14,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f59])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    r1_xboole_0(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f54])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (22129)------------------------------
% 0.20/0.48  % (22129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22129)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (22129)Memory used [KB]: 6268
% 0.20/0.48  % (22129)Time elapsed: 0.055 s
% 0.20/0.48  % (22129)------------------------------
% 0.20/0.48  % (22129)------------------------------
% 0.20/0.48  % (22123)Success in time 0.116 s
%------------------------------------------------------------------------------
