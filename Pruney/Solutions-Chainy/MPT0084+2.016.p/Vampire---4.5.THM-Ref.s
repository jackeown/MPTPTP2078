%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 251 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f51,f57,f71,f97,f207,f216])).

fof(f216,plain,
    ( spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f215,f203,f42])).

fof(f42,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f203,plain,
    ( spl3_18
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f215,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(superposition,[],[f27,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f207,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f196,f94,f54,f48,f203])).

fof(f48,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f94,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f196,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f56,f171])).

fof(f171,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(X0,sK2))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f169,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f169,plain,
    ( ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k3_xboole_0(sK2,X1))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f164,f161])).

fof(f161,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f58,f101])).

fof(f101,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f98,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f98,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl3_11 ),
    inference(superposition,[],[f30,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f58,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f164,plain,
    ( ! [X1] : k3_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK2,X1))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f161,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f56,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f97,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f92,f68,f48,f94])).

fof(f68,plain,
    ( spl3_7
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f75,f50])).

fof(f75,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)
    | ~ spl3_7 ),
    inference(superposition,[],[f24,f70])).

fof(f70,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f66,f48,f68])).

fof(f66,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f60,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f60,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f23,f50])).

fof(f57,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f52,f32,f54])).

fof(f32,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f51,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f37,f48])).

fof(f37,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f39,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f45,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3326)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (3339)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (3327)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (3330)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (3335)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (3340)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (3337)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (3332)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (3341)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (3337)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f35,f40,f45,f51,f57,f71,f97,f207,f216])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    spl3_3 | ~spl3_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f215,f203,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    spl3_18 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) | ~spl3_18),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f212])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl3_18),
% 0.20/0.47    inference(superposition,[],[f27,f205])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f203])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    spl3_18 | ~spl3_4 | ~spl3_5 | ~spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f196,f94,f54,f48,f203])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.47    inference(superposition,[],[f56,f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(X0,sK2))) ) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(superposition,[],[f169,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k3_xboole_0(sK2,X1))) ) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f164,f161])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0)) ) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f58,f101])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X0] : (k3_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl3_11),
% 0.20/0.47    inference(forward_demodulation,[],[f98,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl3_11),
% 0.20/0.47    inference(superposition,[],[f30,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f94])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl3_4),
% 0.20/0.47    inference(superposition,[],[f30,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X1] : (k3_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK2,X1))) ) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(superposition,[],[f161,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl3_11 | ~spl3_4 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f92,f68,f48,f94])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_7 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_4 | ~spl3_7)),
% 0.20/0.47    inference(forward_demodulation,[],[f75,f50])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) | ~spl3_7),
% 0.20/0.47    inference(superposition,[],[f24,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl3_7 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f48,f68])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_4),
% 0.20/0.47    inference(forward_demodulation,[],[f60,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 0.20/0.47    inference(superposition,[],[f23,f50])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl3_5 | ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f32,f54])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    spl3_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.47    inference(resolution,[],[f34,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f32])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl3_4 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f37,f48])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f39,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f42])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f37])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    r1_tarski(sK0,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f32])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (3337)------------------------------
% 0.20/0.47  % (3337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3337)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (3337)Memory used [KB]: 10746
% 0.20/0.47  % (3337)Time elapsed: 0.053 s
% 0.20/0.47  % (3337)------------------------------
% 0.20/0.47  % (3337)------------------------------
% 0.20/0.47  % (3323)Success in time 0.114 s
%------------------------------------------------------------------------------
