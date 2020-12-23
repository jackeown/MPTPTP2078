%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  79 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 166 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f951,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f939,f950])).

fof(f950,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f949])).

fof(f949,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f488,f34])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f488,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f429,f36])).

fof(f36,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f429,plain,(
    ! [X6,X4,X5] : r1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X5,X6)),X6) ),
    inference(superposition,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f939,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f938])).

fof(f938,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f38,f937])).

fof(f937,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f936,f46])).

fof(f46,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(resolution,[],[f43,f23])).

fof(f43,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f19,f40])).

fof(f40,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f25,f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f936,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f912,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f912,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f422,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f25,f19])).

fof(f422,plain,(
    ! [X18] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X18)) = k4_xboole_0(sK0,X18) ),
    inference(superposition,[],[f26,f36])).

fof(f38,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f32,f28])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (5008)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (5004)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (5009)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (5014)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (5015)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (5017)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (5020)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (5006)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (5007)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (5011)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (5013)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (5020)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f951,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f35,f939,f950])).
% 0.20/0.49  fof(f950,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f949])).
% 0.20/0.49  fof(f949,plain,(
% 0.20/0.49    $false | spl3_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f488,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f488,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(superposition,[],[f429,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(resolution,[],[f23,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.49  fof(f429,plain,(
% 0.20/0.49    ( ! [X6,X4,X5] : (r1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X5,X6)),X6)) )),
% 0.20/0.49    inference(superposition,[],[f18,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.49  fof(f939,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f938])).
% 0.20/0.49  fof(f938,plain,(
% 0.20/0.49    $false | spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f38,f937])).
% 0.20/0.49  fof(f937,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(forward_demodulation,[],[f936,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.49    inference(resolution,[],[f43,f23])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    r1_tarski(k1_xboole_0,sK0)),
% 0.20/0.49    inference(superposition,[],[f19,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(resolution,[],[f25,f16])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f936,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.49    inference(forward_demodulation,[],[f912,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f912,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.49    inference(superposition,[],[f422,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(resolution,[],[f25,f19])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    ( ! [X18] : (k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X18)) = k4_xboole_0(sK0,X18)) )),
% 0.20/0.49    inference(superposition,[],[f26,f36])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(resolution,[],[f24,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f32,f28])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5020)------------------------------
% 0.20/0.49  % (5020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5020)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5020)Memory used [KB]: 6524
% 0.20/0.49  % (5020)Time elapsed: 0.081 s
% 0.20/0.49  % (5020)------------------------------
% 0.20/0.49  % (5020)------------------------------
% 0.20/0.49  % (5005)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (5001)Success in time 0.129 s
%------------------------------------------------------------------------------
