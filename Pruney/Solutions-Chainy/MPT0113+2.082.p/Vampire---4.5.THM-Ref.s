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
% DateTime   : Thu Dec  3 12:32:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 155 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   21
%              Number of atoms          :  101 ( 285 expanded)
%              Number of equality atoms :   44 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f1070,f1278])).

fof(f1278,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f1277])).

fof(f1277,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f1071,f1276])).

fof(f1276,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1269,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1269,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f28,f1236])).

fof(f1236,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f1220,f46])).

fof(f46,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1220,plain,(
    ! [X54] : k3_xboole_0(sK0,X54) = k3_xboole_0(sK0,k4_xboole_0(X54,sK2)) ),
    inference(forward_demodulation,[],[f1219,f392])).

fof(f392,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f386,f24])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f386,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f28,f365])).

fof(f365,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f351,f201])).

fof(f201,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f197,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f197,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f184,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f184,plain,(
    ! [X17,X15,X16] : r1_xboole_0(k3_xboole_0(X15,k4_xboole_0(X16,X17)),X17) ),
    inference(superposition,[],[f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f351,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f228,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f228,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(resolution,[],[f214,f30])).

fof(f214,plain,(
    ! [X8,X9] : r1_xboole_0(k3_xboole_0(X9,k1_xboole_0),X8) ),
    inference(superposition,[],[f184,f202])).

fof(f202,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f173,f201])).

fof(f173,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f34,f53])).

fof(f53,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f47,f51])).

fof(f51,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1219,plain,(
    ! [X54] : k3_xboole_0(sK0,k4_xboole_0(X54,sK2)) = k3_xboole_0(sK0,k4_xboole_0(X54,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1125,f34])).

fof(f1125,plain,(
    ! [X54] : k3_xboole_0(sK0,k4_xboole_0(X54,sK2)) = k4_xboole_0(k3_xboole_0(sK0,X54),k1_xboole_0) ),
    inference(superposition,[],[f36,f199])).

fof(f199,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f198,f30])).

fof(f198,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f184,f46])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1071,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1070,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f198,f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42,f38])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (28096)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (28102)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (28100)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (28098)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (28107)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (28109)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (28103)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (28095)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (28097)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (28106)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (28105)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (28092)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (28093)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (28094)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (28108)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (28099)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.53  % (28101)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.54  % (28104)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.56  % (28108)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1281,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f45,f1070,f1278])).
% 0.22/0.56  fof(f1278,plain,(
% 0.22/0.56    spl3_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1277])).
% 0.22/0.56  fof(f1277,plain,(
% 0.22/0.56    $false | spl3_1),
% 0.22/0.56    inference(subsumption_resolution,[],[f1071,f1276])).
% 0.22/0.56  fof(f1276,plain,(
% 0.22/0.56    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f1269,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.56  fof(f1269,plain,(
% 0.22/0.56    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)),
% 0.22/0.56    inference(superposition,[],[f28,f1236])).
% 0.22/0.56  fof(f1236,plain,(
% 0.22/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.56    inference(superposition,[],[f1220,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.56    inference(resolution,[],[f29,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.56  fof(f1220,plain,(
% 0.22/0.56    ( ! [X54] : (k3_xboole_0(sK0,X54) = k3_xboole_0(sK0,k4_xboole_0(X54,sK2))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f1219,f392])).
% 0.22/0.56  fof(f392,plain,(
% 0.22/0.56    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 0.22/0.56    inference(forward_demodulation,[],[f386,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.56  fof(f386,plain,(
% 0.22/0.56    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f28,f365])).
% 0.22/0.56  fof(f365,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f351,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f197,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.56  fof(f197,plain,(
% 0.22/0.56    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.56    inference(superposition,[],[f184,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.56    inference(resolution,[],[f30,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    ( ! [X17,X15,X16] : (r1_xboole_0(k3_xboole_0(X15,k4_xboole_0(X16,X17)),X17)) )),
% 0.22/0.56    inference(superposition,[],[f25,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.56  fof(f351,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 0.22/0.56    inference(superposition,[],[f228,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 0.22/0.56    inference(resolution,[],[f214,f30])).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    ( ! [X8,X9] : (r1_xboole_0(k3_xboole_0(X9,k1_xboole_0),X8)) )),
% 0.22/0.56    inference(superposition,[],[f184,f202])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f173,f201])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,sK2),X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.56    inference(superposition,[],[f34,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 0.22/0.56    inference(superposition,[],[f47,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.56    inference(resolution,[],[f33,f21])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.56  fof(f1219,plain,(
% 0.22/0.56    ( ! [X54] : (k3_xboole_0(sK0,k4_xboole_0(X54,sK2)) = k3_xboole_0(sK0,k4_xboole_0(X54,k1_xboole_0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f1125,f34])).
% 0.22/0.56  fof(f1125,plain,(
% 0.22/0.56    ( ! [X54] : (k3_xboole_0(sK0,k4_xboole_0(X54,sK2)) = k4_xboole_0(k3_xboole_0(sK0,X54),k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f36,f199])).
% 0.22/0.56  fof(f199,plain,(
% 0.22/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.22/0.56    inference(resolution,[],[f198,f30])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    r1_xboole_0(sK0,sK2)),
% 0.22/0.56    inference(superposition,[],[f184,f46])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.56  fof(f1071,plain,(
% 0.22/0.56    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_1),
% 0.22/0.56    inference(resolution,[],[f40,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.56  fof(f1070,plain,(
% 0.22/0.56    spl3_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1069])).
% 0.22/0.56  fof(f1069,plain,(
% 0.22/0.56    $false | spl3_2),
% 0.22/0.56    inference(subsumption_resolution,[],[f198,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ~spl3_1 | ~spl3_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f22,f42,f38])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (28108)------------------------------
% 0.22/0.56  % (28108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28108)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (28108)Memory used [KB]: 6908
% 0.22/0.56  % (28108)Time elapsed: 0.146 s
% 0.22/0.56  % (28108)------------------------------
% 0.22/0.56  % (28108)------------------------------
% 0.22/0.56  % (28091)Success in time 0.201 s
%------------------------------------------------------------------------------
