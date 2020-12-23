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
% DateTime   : Thu Dec  3 12:32:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 130 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  154 ( 246 expanded)
%              Number of equality atoms :   52 (  88 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f57,f62,f69,f79,f105,f114,f120,f129,f488,f525,f527])).

fof(f527,plain,
    ( k3_xboole_0(sK1,sK2) != k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | k3_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))
    | sK2 != k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))
    | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f525,plain,
    ( spl3_34
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f515,f485,f522])).

fof(f522,plain,
    ( spl3_34
  <=> k3_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f485,plain,
    ( spl3_30
  <=> r1_tarski(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f515,plain,
    ( k3_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_30 ),
    inference(resolution,[],[f487,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f487,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f485])).

fof(f488,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f476,f102,f46,f485])).

fof(f46,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( spl3_7
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f476,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(superposition,[],[f461,f104])).

fof(f104,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f461,plain,
    ( ! [X4] : r1_tarski(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X4))
    | ~ spl3_2 ),
    inference(superposition,[],[f29,f140])).

fof(f140,plain,
    ( ! [X6] : k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK2,X6),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f32,f83])).

fof(f83,plain,
    ( ! [X3] : sK1 = k2_xboole_0(k4_xboole_0(sK2,X3),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f80,f33])).

fof(f80,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f50,f29])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f48,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f129,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f123,f111,f126])).

fof(f126,plain,
    ( spl3_10
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f111,plain,
    ( spl3_8
  <=> r1_tarski(k4_xboole_0(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f123,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))
    | ~ spl3_8 ),
    inference(resolution,[],[f113,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f113,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f115,f76,f117])).

fof(f117,plain,
    ( spl3_9
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( spl3_6
  <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f115,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f109,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f109,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))
    | ~ spl3_6 ),
    inference(superposition,[],[f31,f78])).

fof(f78,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f114,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f108,f76,f111])).

fof(f108,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_6 ),
    inference(superposition,[],[f29,f78])).

fof(f105,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f100,f54,f102])).

fof(f54,plain,
    ( spl3_3
  <=> sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f98,f31])).

fof(f98,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f32,f56])).

fof(f56,plain,
    ( sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f79,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f73,f59,f76])).

fof(f59,plain,
    ( spl3_4
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f32,f61])).

fof(f61,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f64,f41,f66])).

fof(f66,plain,
    ( spl3_5
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f41,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f63,f31])).

fof(f63,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(superposition,[],[f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f43,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f62,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f46,f59])).

fof(f52,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f48,f33])).

fof(f57,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f46,f54])).

fof(f51,plain,
    ( sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f48,f34])).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f44,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f41])).

fof(f27,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.40  % (736)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (734)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (727)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (725)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (726)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (737)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (732)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (729)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (734)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f528,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f44,f49,f57,f62,f69,f79,f105,f114,f120,f129,f488,f525,f527])).
% 0.20/0.47  fof(f527,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK2) != k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | k3_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) | sK2 != k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) | k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f525,plain,(
% 0.20/0.47    spl3_34 | ~spl3_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f515,f485,f522])).
% 0.20/0.47  fof(f522,plain,(
% 0.20/0.47    spl3_34 <=> k3_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.47  fof(f485,plain,(
% 0.20/0.47    spl3_30 <=> r1_tarski(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f515,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) | ~spl3_30),
% 0.20/0.47    inference(resolution,[],[f487,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f487,plain,(
% 0.20/0.47    r1_tarski(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) | ~spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f485])).
% 0.20/0.47  fof(f488,plain,(
% 0.20/0.47    spl3_30 | ~spl3_2 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f476,f102,f46,f485])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_7 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f476,plain,(
% 0.20/0.47    r1_tarski(k4_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_7)),
% 0.20/0.47    inference(superposition,[],[f461,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  fof(f461,plain,(
% 0.20/0.47    ( ! [X4] : (r1_tarski(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X4))) ) | ~spl3_2),
% 0.20/0.47    inference(superposition,[],[f29,f140])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X6] : (k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK2,X6),sK1)) ) | ~spl3_2),
% 0.20/0.47    inference(superposition,[],[f32,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X3] : (sK1 = k2_xboole_0(k4_xboole_0(sK2,X3),sK1)) ) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f80,f33])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,X0),sK1)) ) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f50,f29])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f48,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl3_10 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f123,f111,f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl3_10 <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl3_8 <=> r1_tarski(k4_xboole_0(sK1,sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) | ~spl3_8),
% 0.20/0.47    inference(resolution,[],[f113,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl3_9 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f115,f76,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl3_9 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_6 <=> k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | ~spl3_6),
% 0.20/0.47    inference(forward_demodulation,[],[f109,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) | ~spl3_6),
% 0.20/0.47    inference(superposition,[],[f31,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl3_8 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f108,f76,f111])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~spl3_6),
% 0.20/0.47    inference(superposition,[],[f29,f78])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl3_7 | ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f100,f54,f102])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_3 <=> sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.47    inference(forward_demodulation,[],[f98,f31])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.47    inference(superposition,[],[f32,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl3_6 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f73,f59,f76])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl3_4 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_4),
% 0.20/0.47    inference(superposition,[],[f32,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~spl3_5 | spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f64,f41,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl3_5 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl3_1 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.47    inference(forward_demodulation,[],[f63,f31])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_1),
% 0.20/0.47    inference(superposition,[],[f43,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_4 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f46,f59])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f48,f33])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl3_3 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f46,f54])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f48,f34])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f46])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    r1_tarski(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.20/0.47    inference(negated_conjecture,[],[f13])).
% 0.20/0.47  fof(f13,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f41])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (734)------------------------------
% 0.20/0.47  % (734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (734)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (734)Memory used [KB]: 10874
% 0.20/0.47  % (734)Time elapsed: 0.055 s
% 0.20/0.47  % (734)------------------------------
% 0.20/0.47  % (734)------------------------------
% 0.20/0.47  % (722)Success in time 0.121 s
%------------------------------------------------------------------------------
