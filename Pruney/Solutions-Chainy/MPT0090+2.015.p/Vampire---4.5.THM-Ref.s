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
% DateTime   : Thu Dec  3 12:31:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 125 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  184 ( 289 expanded)
%              Number of equality atoms :   56 (  96 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f32,f36,f40,f44,f48,f56,f60,f64,f68,f83,f93,f110,f127,f176,f237])).

fof(f237,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f235,f30])).

fof(f30,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f235,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f229,f35])).

fof(f35,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f229,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_13
    | ~ spl2_26 ),
    inference(superposition,[],[f175,f82])).

fof(f82,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_13
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f175,plain,
    ( ! [X7] : k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k4_xboole_0(sK0,X7)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_26
  <=> ! [X7] : k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k4_xboole_0(sK0,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f176,plain,
    ( spl2_26
    | ~ spl2_9
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f172,f125,f107,f58,f174])).

fof(f58,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f107,plain,
    ( spl2_18
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f125,plain,
    ( spl2_20
  <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f172,plain,
    ( ! [X7] : k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k4_xboole_0(sK0,X7)
    | ~ spl2_9
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f145,f126])).

fof(f126,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f125])).

fof(f145,plain,
    ( ! [X7] : k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X7),k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_18 ),
    inference(superposition,[],[f59,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f107])).

fof(f59,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f127,plain,
    ( spl2_20
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f122,f91,f46,f125])).

fof(f46,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f91,plain,
    ( spl2_14
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f122,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f47,f92])).

fof(f92,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f47,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f110,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f89,f54,f24,f107])).

fof(f24,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f54,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f89,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(resolution,[],[f55,f25])).

fof(f25,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f93,plain,
    ( spl2_14
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f85,f66,f54,f91])).

fof(f66,plain,
    ( spl2_10
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f85,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f55,f67])).

fof(f67,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f75,f46,f42,f81])).

fof(f42,plain,
    ( spl2_5
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f75,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f43,f47])).

fof(f43,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f68,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f62,f38,f34,f66])).

fof(f38,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f62,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f39,f35])).

fof(f39,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f64,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f61,f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f61,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f39,f29])).

fof(f29,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f60,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f56,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f48,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f44,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f36,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f14,f28,f24])).

fof(f14,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f31,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f28,f24])).

fof(f15,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.39  % (29087)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (29083)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (29086)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (29079)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (29081)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (29083)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f239,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f31,f32,f36,f40,f44,f48,f56,f60,f64,f68,f83,f93,f110,f127,f176,f237])).
% 0.21/0.43  fof(f237,plain,(
% 0.21/0.43    spl2_2 | ~spl2_3 | ~spl2_13 | ~spl2_26),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.43  fof(f236,plain,(
% 0.21/0.43    $false | (spl2_2 | ~spl2_3 | ~spl2_13 | ~spl2_26)),
% 0.21/0.43    inference(subsumption_resolution,[],[f235,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    sK0 != k4_xboole_0(sK0,sK1) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl2_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    sK0 = k4_xboole_0(sK0,sK1) | (~spl2_3 | ~spl2_13 | ~spl2_26)),
% 0.21/0.43    inference(forward_demodulation,[],[f229,f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl2_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f229,plain,(
% 0.21/0.43    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl2_13 | ~spl2_26)),
% 0.21/0.43    inference(superposition,[],[f175,f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl2_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl2_13 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.43  fof(f175,plain,(
% 0.21/0.43    ( ! [X7] : (k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k4_xboole_0(sK0,X7)) ) | ~spl2_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f174])).
% 0.21/0.43  fof(f174,plain,(
% 0.21/0.43    spl2_26 <=> ! [X7] : k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k4_xboole_0(sK0,X7)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    spl2_26 | ~spl2_9 | ~spl2_18 | ~spl2_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f172,f125,f107,f58,f174])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl2_9 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    spl2_18 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    spl2_20 <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    ( ! [X7] : (k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k4_xboole_0(sK0,X7)) ) | (~spl2_9 | ~spl2_18 | ~spl2_20)),
% 0.21/0.43    inference(forward_demodulation,[],[f145,f126])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl2_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f125])).
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    ( ! [X7] : (k4_xboole_0(sK0,k4_xboole_0(X7,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X7),k1_xboole_0)) ) | (~spl2_9 | ~spl2_18)),
% 0.21/0.43    inference(superposition,[],[f59,f109])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl2_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f107])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl2_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    spl2_20 | ~spl2_6 | ~spl2_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f122,f91,f46,f125])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl2_14 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl2_6 | ~spl2_14)),
% 0.21/0.43    inference(superposition,[],[f47,f92])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f91])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    spl2_18 | ~spl2_1 | ~spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f89,f54,f24,f107])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl2_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl2_1 | ~spl2_8)),
% 0.21/0.43    inference(resolution,[],[f55,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK1) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f24])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl2_14 | ~spl2_8 | ~spl2_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f66,f54,f91])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl2_10 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl2_8 | ~spl2_10)),
% 0.21/0.43    inference(resolution,[],[f55,f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl2_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f66])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl2_13 | ~spl2_5 | ~spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f75,f46,f42,f81])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl2_5 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.43    inference(superposition,[],[f43,f47])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl2_10 | ~spl2_3 | ~spl2_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f62,f38,f34,f66])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl2_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.43    inference(superposition,[],[f39,f35])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl2_1 | ~spl2_2 | ~spl2_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    $false | (spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.21/0.43    inference(subsumption_resolution,[],[f61,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f24])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK1) | (~spl2_2 | ~spl2_4)),
% 0.21/0.43    inference(superposition,[],[f39,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f58])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f54])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f46])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl2_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f38])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl2_1 | spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f14,f28,f24])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f28,f24])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29083)------------------------------
% 0.21/0.44  % (29083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29083)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29083)Memory used [KB]: 10618
% 0.21/0.44  % (29083)Time elapsed: 0.029 s
% 0.21/0.44  % (29083)------------------------------
% 0.21/0.44  % (29083)------------------------------
% 0.21/0.44  % (29084)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (29089)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.44  % (29077)Success in time 0.086 s
%------------------------------------------------------------------------------
