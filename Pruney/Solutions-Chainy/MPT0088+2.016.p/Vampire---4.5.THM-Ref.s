%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 7.15s
% Output     : Refutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 122 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 228 expanded)
%              Number of equality atoms :   30 (  66 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13608,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f118,f123,f699,f704,f9295,f12228,f13419,f13607])).

fof(f13607,plain,
    ( spl3_12
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f13606])).

fof(f13606,plain,
    ( $false
    | spl3_12
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f13605,f698])).

fof(f698,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f696])).

fof(f696,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f13605,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f13604,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f13604,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f13598,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f13598,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl3_38 ),
    inference(resolution,[],[f13418,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f13418,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f13416])).

fof(f13416,plain,
    ( spl3_38
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f13419,plain,
    ( spl3_38
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f12848,f12225,f13416])).

fof(f12225,plain,
    ( spl3_37
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f12848,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f12227,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f12227,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f12225])).

fof(f12228,plain,
    ( spl3_37
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f9556,f9292,f12225])).

fof(f9292,plain,
    ( spl3_28
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f9556,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f9294,f463])).

fof(f463,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k4_xboole_0(X4,X2),k4_xboole_0(X3,X2))
      | k1_xboole_0 != k4_xboole_0(X4,k2_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3)))) ) ),
    inference(superposition,[],[f105,f29])).

fof(f105,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4))))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f94,f35])).

fof(f94,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f37,f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9294,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f9292])).

fof(f9295,plain,
    ( spl3_28
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f761,f701,f9292])).

fof(f701,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f761,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))
    | ~ spl3_13 ),
    inference(superposition,[],[f703,f35])).

fof(f703,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f701])).

fof(f704,plain,
    ( spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f131,f120,f701])).

fof(f120,plain,
    ( spl3_4
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f127,f35])).

fof(f127,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f122,f38])).

fof(f122,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f699,plain,
    ( ~ spl3_12
    | spl3_3 ),
    inference(avatar_split_clause,[],[f126,f115,f696])).

fof(f115,plain,
    ( spl3_3
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f124,f35])).

fof(f124,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f117,f37])).

fof(f117,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f123,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f55,f41,f120])).

fof(f41,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f43,f30])).

fof(f43,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f118,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f54,f46,f115])).

fof(f46,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f48,f30])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (16086)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (16074)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (16087)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (16077)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (16079)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (16085)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (16085)Refutation not found, incomplete strategy% (16085)------------------------------
% 0.21/0.48  % (16085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16085)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16085)Memory used [KB]: 10618
% 0.21/0.48  % (16085)Time elapsed: 0.069 s
% 0.21/0.48  % (16085)------------------------------
% 0.21/0.48  % (16085)------------------------------
% 0.21/0.48  % (16082)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (16080)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (16078)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (16090)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (16083)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (16084)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (16076)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (16088)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (16089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (16075)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (16091)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (16081)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 4.81/1.02  % (16078)Time limit reached!
% 4.81/1.02  % (16078)------------------------------
% 4.81/1.02  % (16078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.02  % (16078)Termination reason: Time limit
% 4.81/1.02  % (16078)Termination phase: Saturation
% 4.81/1.02  
% 4.81/1.02  % (16078)Memory used [KB]: 13944
% 4.81/1.02  % (16078)Time elapsed: 0.600 s
% 4.81/1.02  % (16078)------------------------------
% 4.81/1.02  % (16078)------------------------------
% 7.15/1.30  % (16089)Refutation found. Thanks to Tanya!
% 7.15/1.30  % SZS status Theorem for theBenchmark
% 7.15/1.31  % SZS output start Proof for theBenchmark
% 7.15/1.31  fof(f13608,plain,(
% 7.15/1.31    $false),
% 7.15/1.31    inference(avatar_sat_refutation,[],[f44,f49,f118,f123,f699,f704,f9295,f12228,f13419,f13607])).
% 7.15/1.31  fof(f13607,plain,(
% 7.15/1.31    spl3_12 | ~spl3_38),
% 7.15/1.31    inference(avatar_contradiction_clause,[],[f13606])).
% 7.15/1.31  fof(f13606,plain,(
% 7.15/1.31    $false | (spl3_12 | ~spl3_38)),
% 7.15/1.31    inference(subsumption_resolution,[],[f13605,f698])).
% 7.15/1.31  fof(f698,plain,(
% 7.15/1.31    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | spl3_12),
% 7.15/1.31    inference(avatar_component_clause,[],[f696])).
% 7.15/1.31  fof(f696,plain,(
% 7.15/1.31    spl3_12 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 7.15/1.31  fof(f13605,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | ~spl3_38),
% 7.15/1.31    inference(forward_demodulation,[],[f13604,f29])).
% 7.15/1.31  fof(f29,plain,(
% 7.15/1.31    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.15/1.31    inference(cnf_transformation,[],[f7])).
% 7.15/1.31  fof(f7,axiom,(
% 7.15/1.31    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.15/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 7.15/1.31  fof(f13604,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~spl3_38),
% 7.15/1.31    inference(forward_demodulation,[],[f13598,f35])).
% 7.15/1.31  fof(f35,plain,(
% 7.15/1.31    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.15/1.31    inference(cnf_transformation,[],[f9])).
% 7.15/1.31  fof(f9,axiom,(
% 7.15/1.31    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.15/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.15/1.31  fof(f13598,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) | ~spl3_38),
% 7.15/1.31    inference(resolution,[],[f13418,f38])).
% 7.15/1.31  fof(f38,plain,(
% 7.15/1.31    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.15/1.31    inference(definition_unfolding,[],[f31,f28])).
% 7.15/1.31  fof(f28,plain,(
% 7.15/1.31    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.15/1.31    inference(cnf_transformation,[],[f10])).
% 7.15/1.31  fof(f10,axiom,(
% 7.15/1.31    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.15/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 7.15/1.31  fof(f31,plain,(
% 7.15/1.31    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.15/1.31    inference(cnf_transformation,[],[f19])).
% 7.15/1.31  fof(f19,plain,(
% 7.15/1.31    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.15/1.31    inference(nnf_transformation,[],[f1])).
% 7.15/1.31  fof(f1,axiom,(
% 7.15/1.31    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.15/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 7.15/1.31  fof(f13418,plain,(
% 7.15/1.31    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_38),
% 7.15/1.31    inference(avatar_component_clause,[],[f13416])).
% 7.15/1.31  fof(f13416,plain,(
% 7.15/1.31    spl3_38 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 7.15/1.31  fof(f13419,plain,(
% 7.15/1.31    spl3_38 | ~spl3_37),
% 7.15/1.31    inference(avatar_split_clause,[],[f12848,f12225,f13416])).
% 7.15/1.31  fof(f12225,plain,(
% 7.15/1.31    spl3_37 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 7.15/1.31  fof(f12848,plain,(
% 7.15/1.31    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_37),
% 7.15/1.31    inference(unit_resulting_resolution,[],[f12227,f30])).
% 7.15/1.31  fof(f30,plain,(
% 7.15/1.31    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 7.15/1.31    inference(cnf_transformation,[],[f16])).
% 7.15/1.31  fof(f16,plain,(
% 7.15/1.31    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.15/1.31    inference(ennf_transformation,[],[f3])).
% 7.15/1.31  fof(f3,axiom,(
% 7.15/1.31    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.15/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 7.15/1.31  fof(f12227,plain,(
% 7.15/1.31    r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) | ~spl3_37),
% 7.15/1.31    inference(avatar_component_clause,[],[f12225])).
% 7.15/1.31  fof(f12228,plain,(
% 7.15/1.31    spl3_37 | ~spl3_28),
% 7.15/1.31    inference(avatar_split_clause,[],[f9556,f9292,f12225])).
% 7.15/1.31  fof(f9292,plain,(
% 7.15/1.31    spl3_28 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 7.15/1.31  fof(f9556,plain,(
% 7.15/1.31    r1_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK2)) | ~spl3_28),
% 7.15/1.31    inference(unit_resulting_resolution,[],[f9294,f463])).
% 7.15/1.31  fof(f463,plain,(
% 7.15/1.31    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X4,X2),k4_xboole_0(X3,X2)) | k1_xboole_0 != k4_xboole_0(X4,k2_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))))) )),
% 7.15/1.31    inference(superposition,[],[f105,f29])).
% 7.15/1.31  fof(f105,plain,(
% 7.15/1.31    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 7.15/1.31    inference(forward_demodulation,[],[f94,f35])).
% 7.15/1.31  fof(f94,plain,(
% 7.15/1.31    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 7.15/1.31    inference(superposition,[],[f37,f35])).
% 7.15/1.31  fof(f37,plain,(
% 7.15/1.31    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.15/1.31    inference(definition_unfolding,[],[f32,f28])).
% 7.15/1.31  fof(f32,plain,(
% 7.15/1.31    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.15/1.31    inference(cnf_transformation,[],[f19])).
% 7.15/1.31  fof(f9294,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) | ~spl3_28),
% 7.15/1.31    inference(avatar_component_clause,[],[f9292])).
% 7.15/1.31  fof(f9295,plain,(
% 7.15/1.31    spl3_28 | ~spl3_13),
% 7.15/1.31    inference(avatar_split_clause,[],[f761,f701,f9292])).
% 7.15/1.31  fof(f701,plain,(
% 7.15/1.31    spl3_13 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 7.15/1.31  fof(f761,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) | ~spl3_13),
% 7.15/1.31    inference(superposition,[],[f703,f35])).
% 7.15/1.31  fof(f703,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))) | ~spl3_13),
% 7.15/1.31    inference(avatar_component_clause,[],[f701])).
% 7.15/1.31  fof(f704,plain,(
% 7.15/1.31    spl3_13 | ~spl3_4),
% 7.15/1.31    inference(avatar_split_clause,[],[f131,f120,f701])).
% 7.15/1.31  fof(f120,plain,(
% 7.15/1.31    spl3_4 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 7.15/1.31  fof(f131,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))) | ~spl3_4),
% 7.15/1.31    inference(forward_demodulation,[],[f127,f35])).
% 7.15/1.31  fof(f127,plain,(
% 7.15/1.31    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) | ~spl3_4),
% 7.15/1.31    inference(unit_resulting_resolution,[],[f122,f38])).
% 7.15/1.31  fof(f122,plain,(
% 7.15/1.31    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_4),
% 7.15/1.31    inference(avatar_component_clause,[],[f120])).
% 7.15/1.31  fof(f699,plain,(
% 7.15/1.31    ~spl3_12 | spl3_3),
% 7.15/1.31    inference(avatar_split_clause,[],[f126,f115,f696])).
% 7.15/1.31  fof(f115,plain,(
% 7.15/1.31    spl3_3 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 7.15/1.31  fof(f126,plain,(
% 7.15/1.31    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | spl3_3),
% 7.15/1.31    inference(forward_demodulation,[],[f124,f35])).
% 7.15/1.31  fof(f124,plain,(
% 7.15/1.31    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | spl3_3),
% 7.15/1.31    inference(unit_resulting_resolution,[],[f117,f37])).
% 7.15/1.31  fof(f117,plain,(
% 7.15/1.31    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_3),
% 7.15/1.31    inference(avatar_component_clause,[],[f115])).
% 7.15/1.31  fof(f123,plain,(
% 7.15/1.31    spl3_4 | ~spl3_1),
% 7.15/1.31    inference(avatar_split_clause,[],[f55,f41,f120])).
% 7.15/1.31  fof(f41,plain,(
% 7.15/1.31    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 7.15/1.31  fof(f55,plain,(
% 7.15/1.31    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_1),
% 7.15/1.31    inference(unit_resulting_resolution,[],[f43,f30])).
% 7.15/1.31  fof(f43,plain,(
% 7.15/1.31    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 7.15/1.31    inference(avatar_component_clause,[],[f41])).
% 7.15/1.31  fof(f118,plain,(
% 7.15/1.31    ~spl3_3 | spl3_2),
% 7.15/1.31    inference(avatar_split_clause,[],[f54,f46,f115])).
% 7.15/1.31  fof(f46,plain,(
% 7.15/1.31    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.15/1.31    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 7.15/1.31  fof(f54,plain,(
% 7.15/1.31    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 7.15/1.31    inference(unit_resulting_resolution,[],[f48,f30])).
% 7.15/1.31  fof(f48,plain,(
% 7.15/1.31    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 7.15/1.31    inference(avatar_component_clause,[],[f46])).
% 7.15/1.31  fof(f49,plain,(
% 7.15/1.31    ~spl3_2),
% 7.15/1.31    inference(avatar_split_clause,[],[f22,f46])).
% 7.15/1.32  fof(f22,plain,(
% 7.15/1.32    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.15/1.32    inference(cnf_transformation,[],[f18])).
% 7.15/1.32  fof(f18,plain,(
% 7.15/1.32    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.15/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 7.15/1.32  fof(f17,plain,(
% 7.15/1.32    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.15/1.32    introduced(choice_axiom,[])).
% 7.15/1.32  fof(f15,plain,(
% 7.15/1.32    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 7.15/1.32    inference(ennf_transformation,[],[f13])).
% 7.15/1.32  fof(f13,negated_conjecture,(
% 7.15/1.32    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.15/1.32    inference(negated_conjecture,[],[f12])).
% 7.15/1.32  fof(f12,conjecture,(
% 7.15/1.32    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.15/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 7.15/1.32  fof(f44,plain,(
% 7.15/1.32    spl3_1),
% 7.15/1.32    inference(avatar_split_clause,[],[f21,f41])).
% 7.15/1.32  fof(f21,plain,(
% 7.15/1.32    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.15/1.32    inference(cnf_transformation,[],[f18])).
% 7.15/1.32  % SZS output end Proof for theBenchmark
% 7.15/1.32  % (16089)------------------------------
% 7.15/1.32  % (16089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.15/1.32  % (16089)Termination reason: Refutation
% 7.15/1.32  
% 7.15/1.32  % (16089)Memory used [KB]: 21108
% 7.15/1.32  % (16089)Time elapsed: 0.897 s
% 7.15/1.32  % (16089)------------------------------
% 7.15/1.32  % (16089)------------------------------
% 7.15/1.32  % (16073)Success in time 0.963 s
%------------------------------------------------------------------------------
