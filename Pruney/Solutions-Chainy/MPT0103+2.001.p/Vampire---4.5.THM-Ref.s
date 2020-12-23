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
% DateTime   : Thu Dec  3 12:32:00 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  76 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f99,f146,f8198])).

fof(f8198,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f8197])).

fof(f8197,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f8056,f5024])).

fof(f5024,plain,(
    ! [X17,X16] : k1_xboole_0 = k4_xboole_0(X17,k2_xboole_0(X16,k5_xboole_0(X17,X16))) ),
    inference(superposition,[],[f2058,f4964])).

fof(f4964,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f4960,f63])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f4960,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f4912,f107])).

fof(f107,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f4912,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f78,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2058,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X14,X15),k2_xboole_0(X14,X15)) ),
    inference(superposition,[],[f151,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f151,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f8056,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | spl4_3 ),
    inference(superposition,[],[f145,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f145,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_3
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f146,plain,
    ( ~ spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f141,f96,f143])).

fof(f96,plain,
    ( spl4_2
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f141,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(resolution,[],[f75,f98])).

fof(f98,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f40])).

fof(f40,plain,
    ( ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f89,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f51,f86])).

fof(f86,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (2850)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (2835)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (2842)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (2848)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (2836)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (2839)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (2843)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (2834)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (2841)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (2840)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (2851)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (2846)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (2837)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (2852)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (2847)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (2845)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (2847)Refutation not found, incomplete strategy% (2847)------------------------------
% 0.20/0.50  % (2847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2847)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2847)Memory used [KB]: 10618
% 0.20/0.50  % (2847)Time elapsed: 0.086 s
% 0.20/0.50  % (2847)------------------------------
% 0.20/0.50  % (2847)------------------------------
% 0.20/0.51  % (2853)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.31/0.53  % (2849)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 2.59/0.75  % (2834)Refutation found. Thanks to Tanya!
% 2.59/0.75  % SZS status Theorem for theBenchmark
% 2.59/0.75  % SZS output start Proof for theBenchmark
% 2.59/0.75  fof(f8211,plain,(
% 2.59/0.75    $false),
% 2.59/0.75    inference(avatar_sat_refutation,[],[f89,f99,f146,f8198])).
% 2.59/0.75  fof(f8198,plain,(
% 2.59/0.75    spl4_3),
% 2.59/0.75    inference(avatar_contradiction_clause,[],[f8197])).
% 2.59/0.75  fof(f8197,plain,(
% 2.59/0.75    $false | spl4_3),
% 2.59/0.75    inference(subsumption_resolution,[],[f8056,f5024])).
% 2.59/0.75  fof(f5024,plain,(
% 2.59/0.75    ( ! [X17,X16] : (k1_xboole_0 = k4_xboole_0(X17,k2_xboole_0(X16,k5_xboole_0(X17,X16)))) )),
% 2.59/0.75    inference(superposition,[],[f2058,f4964])).
% 2.59/0.75  fof(f4964,plain,(
% 2.59/0.75    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.59/0.75    inference(superposition,[],[f4960,f63])).
% 2.59/0.75  fof(f63,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f2])).
% 2.59/0.75  fof(f2,axiom,(
% 2.59/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.59/0.75  fof(f4960,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.59/0.75    inference(forward_demodulation,[],[f4912,f107])).
% 2.59/0.75  fof(f107,plain,(
% 2.59/0.75    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.59/0.75    inference(superposition,[],[f63,f55])).
% 2.59/0.75  fof(f55,plain,(
% 2.59/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.59/0.75    inference(cnf_transformation,[],[f22])).
% 2.59/0.75  fof(f22,axiom,(
% 2.59/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.59/0.75  fof(f4912,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.59/0.75    inference(superposition,[],[f78,f54])).
% 2.59/0.75  fof(f54,plain,(
% 2.59/0.75    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f29])).
% 2.59/0.75  fof(f29,axiom,(
% 2.59/0.75    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.59/0.75  fof(f78,plain,(
% 2.59/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f28])).
% 2.59/0.75  fof(f28,axiom,(
% 2.59/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.59/0.75  fof(f2058,plain,(
% 2.59/0.75    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X14,X15),k2_xboole_0(X14,X15))) )),
% 2.59/0.75    inference(superposition,[],[f151,f68])).
% 2.59/0.75  fof(f68,plain,(
% 2.59/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f9])).
% 2.59/0.75  fof(f9,axiom,(
% 2.59/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.59/0.75  fof(f151,plain,(
% 2.59/0.75    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 2.59/0.75    inference(resolution,[],[f76,f61])).
% 2.59/0.75  fof(f61,plain,(
% 2.59/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f13])).
% 2.59/0.75  fof(f13,axiom,(
% 2.59/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.59/0.75  fof(f76,plain,(
% 2.59/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f49])).
% 2.59/0.75  fof(f49,plain,(
% 2.59/0.75    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.59/0.75    inference(nnf_transformation,[],[f8])).
% 2.59/0.75  fof(f8,axiom,(
% 2.59/0.75    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.59/0.75  fof(f8056,plain,(
% 2.59/0.75    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | spl4_3),
% 2.59/0.75    inference(superposition,[],[f145,f80])).
% 2.59/0.75  fof(f80,plain,(
% 2.59/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.59/0.75    inference(cnf_transformation,[],[f16])).
% 2.59/0.75  fof(f16,axiom,(
% 2.59/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.59/0.75  fof(f145,plain,(
% 2.59/0.75    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl4_3),
% 2.59/0.75    inference(avatar_component_clause,[],[f143])).
% 2.59/0.75  fof(f143,plain,(
% 2.59/0.75    spl4_3 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.59/0.75  fof(f146,plain,(
% 2.59/0.75    ~spl4_3 | spl4_2),
% 2.59/0.75    inference(avatar_split_clause,[],[f141,f96,f143])).
% 2.59/0.75  fof(f96,plain,(
% 2.59/0.75    spl4_2 <=> r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.59/0.75  fof(f141,plain,(
% 2.59/0.75    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl4_2),
% 2.59/0.75    inference(resolution,[],[f75,f98])).
% 2.59/0.75  fof(f98,plain,(
% 2.59/0.75    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl4_2),
% 2.59/0.75    inference(avatar_component_clause,[],[f96])).
% 2.59/0.75  fof(f75,plain,(
% 2.59/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.59/0.75    inference(cnf_transformation,[],[f49])).
% 2.59/0.75  fof(f99,plain,(
% 2.59/0.75    ~spl4_2),
% 2.59/0.75    inference(avatar_split_clause,[],[f50,f96])).
% 2.59/0.75  fof(f50,plain,(
% 2.59/0.75    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 2.59/0.75    inference(cnf_transformation,[],[f41])).
% 2.59/0.75  fof(f41,plain,(
% 2.59/0.75    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 2.59/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f40])).
% 2.59/0.75  fof(f40,plain,(
% 2.59/0.75    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 2.59/0.75    introduced(choice_axiom,[])).
% 2.59/0.75  fof(f35,plain,(
% 2.59/0.75    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.59/0.75    inference(ennf_transformation,[],[f32])).
% 2.59/0.75  fof(f32,negated_conjecture,(
% 2.59/0.75    ~! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.59/0.75    inference(negated_conjecture,[],[f31])).
% 2.59/0.75  fof(f31,conjecture,(
% 2.59/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 2.59/0.75  fof(f89,plain,(
% 2.59/0.75    spl4_1),
% 2.59/0.75    inference(avatar_split_clause,[],[f51,f86])).
% 2.59/0.75  fof(f86,plain,(
% 2.59/0.75    spl4_1 <=> v1_xboole_0(k1_xboole_0)),
% 2.59/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.59/0.75  fof(f51,plain,(
% 2.59/0.75    v1_xboole_0(k1_xboole_0)),
% 2.59/0.75    inference(cnf_transformation,[],[f4])).
% 2.59/0.75  fof(f4,axiom,(
% 2.59/0.75    v1_xboole_0(k1_xboole_0)),
% 2.59/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.59/0.75  % SZS output end Proof for theBenchmark
% 2.59/0.75  % (2834)------------------------------
% 2.59/0.75  % (2834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.75  % (2834)Termination reason: Refutation
% 2.59/0.75  
% 2.59/0.75  % (2834)Memory used [KB]: 10234
% 2.59/0.75  % (2834)Time elapsed: 0.287 s
% 2.59/0.75  % (2834)------------------------------
% 2.59/0.75  % (2834)------------------------------
% 3.17/0.76  % (2827)Success in time 0.402 s
%------------------------------------------------------------------------------
