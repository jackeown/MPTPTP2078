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
% DateTime   : Thu Dec  3 12:32:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 175 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :   94 ( 315 expanded)
%              Number of equality atoms :   41 ( 115 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f508,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f504,f507])).

fof(f507,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f405,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f405,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f20,f386])).

fof(f386,plain,(
    sK0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f27,f38])).

fof(f38,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f504,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f40,f502])).

fof(f502,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f493,f217])).

fof(f217,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f210,f42])).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f26,f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f210,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f23,f38])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f493,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f23,f459])).

fof(f459,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f458,f386])).

fof(f458,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f449,f370])).

fof(f370,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f362,f192])).

fof(f192,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f185,f119])).

fof(f119,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f89,f24])).

fof(f89,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f185,plain,(
    ! [X4,X5] : k3_xboole_0(k3_xboole_0(X4,X5),X4) = k4_xboole_0(k3_xboole_0(X4,X5),k1_xboole_0) ),
    inference(superposition,[],[f22,f90])).

fof(f90,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f43,f22])).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f26,f21])).

fof(f362,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f23,f329])).

fof(f329,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f327,f22])).

fof(f327,plain,(
    ! [X6,X5] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) ),
    inference(forward_demodulation,[],[f318,f273])).

fof(f273,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f90,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f24,f21])).

fof(f318,plain,(
    ! [X6,X5] : k3_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f22,f95])).

fof(f95,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f82,f39])).

fof(f82,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f22,f43])).

fof(f449,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k5_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f23,f419])).

fof(f419,plain,(
    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f407,f90])).

fof(f407,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f22,f386])).

fof(f40,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f34,f30])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (23582)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (23580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (23576)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (23589)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (23587)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (23579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (23578)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (23585)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (23583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (23592)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (23586)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (23590)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (23591)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (23581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (23584)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (23592)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f508,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f37,f504,f507])).
% 0.20/0.48  fof(f507,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f506])).
% 0.20/0.48  fof(f506,plain,(
% 0.20/0.48    $false | spl3_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f405,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f405,plain,(
% 0.20/0.48    r1_xboole_0(sK0,sK2)),
% 0.20/0.48    inference(superposition,[],[f20,f386])).
% 0.20/0.48  fof(f386,plain,(
% 0.20/0.48    sK0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.20/0.48    inference(superposition,[],[f27,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(resolution,[],[f24,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.48  fof(f504,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f503])).
% 0.20/0.48  fof(f503,plain,(
% 0.20/0.48    $false | spl3_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f40,f502])).
% 0.20/0.48  fof(f502,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.48    inference(forward_demodulation,[],[f493,f217])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.20/0.48    inference(forward_demodulation,[],[f210,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(resolution,[],[f26,f18])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)),
% 0.20/0.48    inference(superposition,[],[f23,f38])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.49  fof(f493,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)),
% 0.20/0.49    inference(superposition,[],[f23,f459])).
% 0.20/0.49  fof(f459,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(forward_demodulation,[],[f458,f386])).
% 0.20/0.49  fof(f458,plain,(
% 0.20/0.49    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f449,f370])).
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f362,f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k1_xboole_0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f185,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 0.20/0.49    inference(resolution,[],[f89,f24])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.20/0.49    inference(superposition,[],[f21,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k3_xboole_0(k3_xboole_0(X4,X5),X4) = k4_xboole_0(k3_xboole_0(X4,X5),k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f22,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X5),X4)) )),
% 0.20/0.49    inference(superposition,[],[f43,f22])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(resolution,[],[f26,f21])).
% 0.20/0.49  fof(f362,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f23,f329])).
% 0.20/0.49  fof(f329,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f327,f22])).
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    ( ! [X6,X5] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f318,f273])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 0.20/0.49    inference(superposition,[],[f90,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(resolution,[],[f24,f21])).
% 0.20/0.49  fof(f318,plain,(
% 0.20/0.49    ( ! [X6,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 0.20/0.49    inference(superposition,[],[f22,f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f82,f39])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f22,f43])).
% 0.20/0.49  fof(f449,plain,(
% 0.20/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k5_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.20/0.49    inference(superposition,[],[f23,f419])).
% 0.20/0.49  fof(f419,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f407,f90])).
% 0.20/0.49  fof(f407,plain,(
% 0.20/0.49    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 0.20/0.49    inference(superposition,[],[f22,f386])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(resolution,[],[f25,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f34,f30])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (23592)------------------------------
% 0.20/0.49  % (23592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23592)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (23592)Memory used [KB]: 6268
% 0.20/0.49  % (23592)Time elapsed: 0.076 s
% 0.20/0.49  % (23592)------------------------------
% 0.20/0.49  % (23592)------------------------------
% 0.20/0.49  % (23577)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (23574)Success in time 0.131 s
%------------------------------------------------------------------------------
