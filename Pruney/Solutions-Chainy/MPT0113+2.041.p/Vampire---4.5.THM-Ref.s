%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:38 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 103 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :   82 ( 187 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f4264,f4269])).

fof(f4269,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f4268])).

fof(f4268,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f547,f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f547,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f496,f52])).

fof(f52,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f496,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k3_xboole_0(X6,k4_xboole_0(X7,X8)),X8) ),
    inference(superposition,[],[f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f4264,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f4263])).

fof(f4263,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f40,f4246])).

fof(f4246,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f46,f4168])).

fof(f4168,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f4024,f52])).

fof(f4024,plain,(
    ! [X90] : k3_xboole_0(sK0,X90) = k3_xboole_0(sK0,k4_xboole_0(X90,sK2)) ),
    inference(forward_demodulation,[],[f4023,f94])).

fof(f94,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f87,f24])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f87,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f30,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f68,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f64,f31])).

fof(f64,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f46,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f32,f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f4023,plain,(
    ! [X90] : k3_xboole_0(sK0,k4_xboole_0(X90,sK2)) = k3_xboole_0(sK0,k4_xboole_0(X90,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f3872,f34])).

fof(f3872,plain,(
    ! [X90] : k3_xboole_0(sK0,k4_xboole_0(X90,sK2)) = k4_xboole_0(k3_xboole_0(sK0,X90),k1_xboole_0) ),
    inference(superposition,[],[f36,f554])).

fof(f554,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f547,f32])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f40,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42,f38])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (18580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (18587)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (18586)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (18575)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (18583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (18581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (18585)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (18584)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (18588)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (18576)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (18579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (18577)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (18592)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (18582)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.28/0.51  % (18589)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.28/0.52  % (18593)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.28/0.52  % (18590)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.28/0.52  % (18591)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.44/0.61  % (18592)Refutation found. Thanks to Tanya!
% 1.44/0.61  % SZS status Theorem for theBenchmark
% 1.44/0.61  % SZS output start Proof for theBenchmark
% 1.44/0.61  fof(f4270,plain,(
% 1.44/0.61    $false),
% 1.44/0.61    inference(avatar_sat_refutation,[],[f45,f4264,f4269])).
% 1.44/0.61  fof(f4269,plain,(
% 1.44/0.61    spl3_2),
% 1.44/0.61    inference(avatar_contradiction_clause,[],[f4268])).
% 1.44/0.61  fof(f4268,plain,(
% 1.44/0.61    $false | spl3_2),
% 1.44/0.61    inference(subsumption_resolution,[],[f547,f44])).
% 1.44/0.61  fof(f44,plain,(
% 1.44/0.61    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 1.44/0.61    inference(avatar_component_clause,[],[f42])).
% 1.44/0.61  fof(f42,plain,(
% 1.44/0.61    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 1.44/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.61  fof(f547,plain,(
% 1.44/0.61    r1_xboole_0(sK0,sK2)),
% 1.44/0.61    inference(superposition,[],[f496,f52])).
% 1.44/0.61  fof(f52,plain,(
% 1.44/0.61    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.44/0.61    inference(resolution,[],[f31,f21])).
% 1.44/0.61  fof(f21,plain,(
% 1.44/0.61    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.44/0.61    inference(cnf_transformation,[],[f19])).
% 1.44/0.61  fof(f19,plain,(
% 1.44/0.61    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.44/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 1.44/0.61  fof(f18,plain,(
% 1.44/0.61    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.44/0.61    introduced(choice_axiom,[])).
% 1.44/0.61  fof(f16,plain,(
% 1.44/0.61    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.44/0.61    inference(ennf_transformation,[],[f15])).
% 1.44/0.61  fof(f15,negated_conjecture,(
% 1.44/0.61    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.44/0.61    inference(negated_conjecture,[],[f14])).
% 1.44/0.61  fof(f14,conjecture,(
% 1.44/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.44/0.61  fof(f31,plain,(
% 1.44/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.44/0.61    inference(cnf_transformation,[],[f17])).
% 1.44/0.61  fof(f17,plain,(
% 1.44/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.61    inference(ennf_transformation,[],[f7])).
% 1.44/0.61  fof(f7,axiom,(
% 1.44/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.61  fof(f496,plain,(
% 1.44/0.61    ( ! [X6,X8,X7] : (r1_xboole_0(k3_xboole_0(X6,k4_xboole_0(X7,X8)),X8)) )),
% 1.44/0.61    inference(superposition,[],[f25,f34])).
% 1.44/0.61  fof(f34,plain,(
% 1.44/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f8])).
% 1.44/0.61  fof(f8,axiom,(
% 1.44/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.44/0.61  fof(f25,plain,(
% 1.44/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f11])).
% 1.44/0.61  fof(f11,axiom,(
% 1.44/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.44/0.61  fof(f4264,plain,(
% 1.44/0.61    spl3_1),
% 1.44/0.61    inference(avatar_contradiction_clause,[],[f4263])).
% 1.44/0.61  fof(f4263,plain,(
% 1.44/0.61    $false | spl3_1),
% 1.44/0.61    inference(subsumption_resolution,[],[f40,f4246])).
% 1.44/0.61  fof(f4246,plain,(
% 1.44/0.61    r1_tarski(sK0,sK1)),
% 1.44/0.61    inference(superposition,[],[f46,f4168])).
% 1.44/0.61  fof(f4168,plain,(
% 1.44/0.61    sK0 = k3_xboole_0(sK0,sK1)),
% 1.44/0.61    inference(superposition,[],[f4024,f52])).
% 1.44/0.61  fof(f4024,plain,(
% 1.44/0.61    ( ! [X90] : (k3_xboole_0(sK0,X90) = k3_xboole_0(sK0,k4_xboole_0(X90,sK2))) )),
% 1.44/0.61    inference(forward_demodulation,[],[f4023,f94])).
% 1.44/0.61  fof(f94,plain,(
% 1.44/0.61    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 1.44/0.61    inference(forward_demodulation,[],[f87,f24])).
% 1.44/0.61  fof(f24,plain,(
% 1.44/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.61    inference(cnf_transformation,[],[f10])).
% 1.44/0.61  fof(f10,axiom,(
% 1.44/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.61  fof(f87,plain,(
% 1.44/0.61    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 1.44/0.61    inference(superposition,[],[f30,f69])).
% 1.44/0.61  fof(f69,plain,(
% 1.44/0.61    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.44/0.61    inference(superposition,[],[f68,f27])).
% 1.44/0.61  fof(f27,plain,(
% 1.44/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f1])).
% 1.44/0.61  fof(f1,axiom,(
% 1.44/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.61  fof(f68,plain,(
% 1.44/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.44/0.61    inference(resolution,[],[f64,f31])).
% 1.44/0.61  fof(f64,plain,(
% 1.44/0.61    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.44/0.61    inference(superposition,[],[f46,f61])).
% 1.44/0.61  fof(f61,plain,(
% 1.44/0.61    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.44/0.61    inference(resolution,[],[f32,f25])).
% 1.44/0.61  fof(f32,plain,(
% 1.44/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.44/0.61    inference(cnf_transformation,[],[f20])).
% 1.44/0.61  fof(f20,plain,(
% 1.44/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.44/0.61    inference(nnf_transformation,[],[f2])).
% 1.44/0.61  fof(f2,axiom,(
% 1.44/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.44/0.61  fof(f30,plain,(
% 1.44/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.61    inference(cnf_transformation,[],[f3])).
% 1.44/0.61  fof(f3,axiom,(
% 1.44/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.61  fof(f4023,plain,(
% 1.44/0.61    ( ! [X90] : (k3_xboole_0(sK0,k4_xboole_0(X90,sK2)) = k3_xboole_0(sK0,k4_xboole_0(X90,k1_xboole_0))) )),
% 1.44/0.61    inference(forward_demodulation,[],[f3872,f34])).
% 1.44/0.61  fof(f3872,plain,(
% 1.44/0.61    ( ! [X90] : (k3_xboole_0(sK0,k4_xboole_0(X90,sK2)) = k4_xboole_0(k3_xboole_0(sK0,X90),k1_xboole_0)) )),
% 1.44/0.61    inference(superposition,[],[f36,f554])).
% 1.44/0.61  fof(f554,plain,(
% 1.44/0.61    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.44/0.61    inference(resolution,[],[f547,f32])).
% 1.44/0.61  fof(f36,plain,(
% 1.44/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.44/0.61    inference(cnf_transformation,[],[f9])).
% 1.44/0.61  fof(f9,axiom,(
% 1.44/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.44/0.61  fof(f46,plain,(
% 1.44/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.44/0.61    inference(superposition,[],[f26,f27])).
% 1.44/0.61  fof(f26,plain,(
% 1.44/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f5])).
% 1.44/0.61  fof(f5,axiom,(
% 1.44/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.44/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.44/0.61  fof(f40,plain,(
% 1.44/0.61    ~r1_tarski(sK0,sK1) | spl3_1),
% 1.44/0.61    inference(avatar_component_clause,[],[f38])).
% 1.44/0.61  fof(f38,plain,(
% 1.44/0.61    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.44/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.61  fof(f45,plain,(
% 1.44/0.61    ~spl3_1 | ~spl3_2),
% 1.44/0.61    inference(avatar_split_clause,[],[f22,f42,f38])).
% 1.44/0.61  fof(f22,plain,(
% 1.44/0.61    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.44/0.61    inference(cnf_transformation,[],[f19])).
% 1.44/0.61  % SZS output end Proof for theBenchmark
% 1.44/0.61  % (18592)------------------------------
% 1.44/0.61  % (18592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.61  % (18592)Termination reason: Refutation
% 1.44/0.61  
% 1.44/0.61  % (18592)Memory used [KB]: 8187
% 1.44/0.61  % (18592)Time elapsed: 0.188 s
% 1.44/0.61  % (18592)------------------------------
% 1.44/0.61  % (18592)------------------------------
% 1.44/0.61  % (18571)Success in time 0.253 s
%------------------------------------------------------------------------------
