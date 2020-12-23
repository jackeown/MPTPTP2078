%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 149 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f2307,f2309])).

fof(f2309,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f2308])).

fof(f2308,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f544,f41])).

fof(f41,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f544,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f504,f51])).

fof(f51,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f504,plain,(
    ! [X6,X4,X5] : r1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X5,X6)),X6) ),
    inference(superposition,[],[f25,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f2307,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2306])).

fof(f2306,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f37,f2299])).

fof(f2299,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f2092,f51])).

fof(f2092,plain,(
    ! [X24,X23,X22] : r1_tarski(k3_xboole_0(X24,k4_xboole_0(X22,X23)),X22) ),
    inference(superposition,[],[f1334,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1334,plain,(
    ! [X28,X29,X27] : r1_tarski(k3_xboole_0(X27,k3_xboole_0(X28,X29)),X29) ),
    inference(superposition,[],[f367,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f367,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f347,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f347,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f26,f198])).

fof(f198,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(backward_demodulation,[],[f114,f187])).

fof(f187,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f178,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f178,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f158,f43])).

fof(f43,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f158,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f31,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f114,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f54,f52])).

fof(f54,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f29,f28])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39,f35])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (14514)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.43  % (14525)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (14522)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (14513)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (14515)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (14521)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (14523)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (14511)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (14527)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (14517)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (14524)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (14518)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (14512)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (14516)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (14526)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (14519)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (14528)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (14520)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.44/0.54  % (14527)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f2310,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(avatar_sat_refutation,[],[f42,f2307,f2309])).
% 1.44/0.54  fof(f2309,plain,(
% 1.44/0.54    spl3_2),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f2308])).
% 1.44/0.54  fof(f2308,plain,(
% 1.44/0.54    $false | spl3_2),
% 1.44/0.54    inference(subsumption_resolution,[],[f544,f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 1.44/0.54    inference(avatar_component_clause,[],[f39])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.54  fof(f544,plain,(
% 1.44/0.54    r1_xboole_0(sK0,sK2)),
% 1.44/0.54    inference(superposition,[],[f504,f51])).
% 1.44/0.54  fof(f51,plain,(
% 1.44/0.54    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.44/0.54    inference(resolution,[],[f30,f20])).
% 1.44/0.54  fof(f20,plain,(
% 1.44/0.54    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.44/0.54    inference(cnf_transformation,[],[f19])).
% 1.44/0.54  fof(f19,plain,(
% 1.44/0.54    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 1.44/0.54  fof(f18,plain,(
% 1.44/0.54    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f16,plain,(
% 1.44/0.54    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.44/0.54    inference(ennf_transformation,[],[f14])).
% 1.44/0.54  fof(f14,negated_conjecture,(
% 1.44/0.54    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.44/0.54    inference(negated_conjecture,[],[f13])).
% 1.44/0.54  fof(f13,conjecture,(
% 1.44/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f17])).
% 1.44/0.54  fof(f17,plain,(
% 1.44/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.54    inference(ennf_transformation,[],[f6])).
% 1.44/0.54  fof(f6,axiom,(
% 1.44/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.54  fof(f504,plain,(
% 1.44/0.54    ( ! [X6,X4,X5] : (r1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X5,X6)),X6)) )),
% 1.44/0.54    inference(superposition,[],[f25,f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.44/0.54  fof(f25,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f10])).
% 1.44/0.54  fof(f10,axiom,(
% 1.44/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.44/0.54  fof(f2307,plain,(
% 1.44/0.54    spl3_1),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f2306])).
% 1.44/0.54  fof(f2306,plain,(
% 1.44/0.54    $false | spl3_1),
% 1.44/0.54    inference(subsumption_resolution,[],[f37,f2299])).
% 1.44/0.54  fof(f2299,plain,(
% 1.44/0.54    r1_tarski(sK0,sK1)),
% 1.44/0.54    inference(superposition,[],[f2092,f51])).
% 1.44/0.54  fof(f2092,plain,(
% 1.44/0.54    ( ! [X24,X23,X22] : (r1_tarski(k3_xboole_0(X24,k4_xboole_0(X22,X23)),X22)) )),
% 1.44/0.54    inference(superposition,[],[f1334,f52])).
% 1.44/0.54  fof(f52,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.44/0.54    inference(resolution,[],[f30,f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f7])).
% 1.44/0.54  fof(f7,axiom,(
% 1.44/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.44/0.54  fof(f1334,plain,(
% 1.44/0.54    ( ! [X28,X29,X27] : (r1_tarski(k3_xboole_0(X27,k3_xboole_0(X28,X29)),X29)) )),
% 1.44/0.54    inference(superposition,[],[f367,f33])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.44/0.54  fof(f367,plain,(
% 1.44/0.54    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.44/0.54    inference(superposition,[],[f347,f28])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f1])).
% 1.44/0.54  fof(f1,axiom,(
% 1.44/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.54  fof(f347,plain,(
% 1.44/0.54    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 1.44/0.54    inference(superposition,[],[f26,f198])).
% 1.44/0.54  fof(f198,plain,(
% 1.44/0.54    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,X7)) )),
% 1.44/0.54    inference(backward_demodulation,[],[f114,f187])).
% 1.44/0.54  fof(f187,plain,(
% 1.44/0.54    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.44/0.54    inference(superposition,[],[f178,f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.54  fof(f178,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.44/0.54    inference(forward_demodulation,[],[f158,f43])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.44/0.54    inference(superposition,[],[f27,f23])).
% 1.44/0.54  fof(f23,plain,(
% 1.44/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.54    inference(cnf_transformation,[],[f9])).
% 1.44/0.54  fof(f9,axiom,(
% 1.44/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f2])).
% 1.44/0.54  fof(f2,axiom,(
% 1.44/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.44/0.54  fof(f158,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.44/0.54    inference(superposition,[],[f31,f22])).
% 1.44/0.54  fof(f22,plain,(
% 1.44/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f12])).
% 1.44/0.54  fof(f12,axiom,(
% 1.44/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f11])).
% 1.44/0.54  fof(f11,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.44/0.54  fof(f114,plain,(
% 1.44/0.54    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 1.44/0.54    inference(superposition,[],[f54,f52])).
% 1.44/0.54  fof(f54,plain,(
% 1.44/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.44/0.54    inference(superposition,[],[f29,f28])).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    ~r1_tarski(sK0,sK1) | spl3_1),
% 1.44/0.54    inference(avatar_component_clause,[],[f35])).
% 1.44/0.54  fof(f35,plain,(
% 1.44/0.54    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    ~spl3_1 | ~spl3_2),
% 1.44/0.54    inference(avatar_split_clause,[],[f21,f39,f35])).
% 1.44/0.54  fof(f21,plain,(
% 1.44/0.54    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.44/0.54    inference(cnf_transformation,[],[f19])).
% 1.44/0.54  % SZS output end Proof for theBenchmark
% 1.44/0.54  % (14527)------------------------------
% 1.44/0.54  % (14527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (14527)Termination reason: Refutation
% 1.44/0.54  
% 1.44/0.54  % (14527)Memory used [KB]: 7419
% 1.44/0.54  % (14527)Time elapsed: 0.111 s
% 1.44/0.54  % (14527)------------------------------
% 1.44/0.54  % (14527)------------------------------
% 1.44/0.54  % (14510)Success in time 0.187 s
%------------------------------------------------------------------------------
