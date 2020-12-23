%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:04 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 162 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   21
%              Number of atoms          :   90 ( 217 expanded)
%              Number of equality atoms :   53 ( 156 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3250,f21])).

fof(f21,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f3250,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3249,f22])).

fof(f22,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f3249,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f3100,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f3100,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f3099])).

fof(f3099,plain,
    ( sK2 != sK2
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f23,f2881])).

fof(f2881,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X3,X4) = X3
      | ~ r1_xboole_0(X4,X3) ) ),
    inference(forward_demodulation,[],[f2859,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f47,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f36])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f31,f24])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f2859,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,X4)
      | ~ r1_xboole_0(X4,X3) ) ),
    inference(superposition,[],[f30,f2777])).

fof(f2777,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f2734,f69])).

fof(f69,plain,(
    ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6) ),
    inference(forward_demodulation,[],[f68,f24])).

fof(f68,plain,(
    ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,X6) ),
    inference(forward_demodulation,[],[f59,f36])).

fof(f59,plain,(
    ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k2_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f32,f48])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f2734,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k5_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f2088,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2088,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f2031,f444])).

fof(f444,plain,(
    ! [X19,X20] : k5_xboole_0(X20,k2_xboole_0(X19,X20)) = k4_xboole_0(X19,X20) ),
    inference(forward_demodulation,[],[f422,f30])).

fof(f422,plain,(
    ! [X19,X20] : k5_xboole_0(X20,k2_xboole_0(X19,X20)) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(superposition,[],[f113,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f34,f32])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f113,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f109,f50])).

fof(f50,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f109,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f69])).

fof(f2031,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(superposition,[],[f176,f116])).

fof(f116,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f176,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k2_xboole_0(X4,X3))) ),
    inference(superposition,[],[f56,f34])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f26])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:15:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (27430)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (27417)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (27420)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (27431)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (27424)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (27434)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (27423)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (27418)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (27428)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (27421)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (27428)Refutation not found, incomplete strategy% (27428)------------------------------
% 0.21/0.49  % (27428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27428)Memory used [KB]: 10618
% 0.21/0.49  % (27428)Time elapsed: 0.080 s
% 0.21/0.49  % (27428)------------------------------
% 0.21/0.49  % (27428)------------------------------
% 0.21/0.50  % (27419)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (27426)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (27425)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (27432)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (27422)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (27429)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (27427)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (27433)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.76/0.75  % (27420)Refutation found. Thanks to Tanya!
% 2.76/0.75  % SZS status Theorem for theBenchmark
% 2.76/0.75  % SZS output start Proof for theBenchmark
% 2.76/0.75  fof(f3251,plain,(
% 2.76/0.75    $false),
% 2.76/0.75    inference(subsumption_resolution,[],[f3250,f21])).
% 2.76/0.75  fof(f21,plain,(
% 2.76/0.75    ~r2_hidden(sK0,sK2)),
% 2.76/0.75    inference(cnf_transformation,[],[f20])).
% 2.76/0.75  fof(f20,plain,(
% 2.76/0.75    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 2.76/0.75  fof(f19,plain,(
% 2.76/0.75    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f16,plain,(
% 2.76/0.75    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.76/0.75    inference(ennf_transformation,[],[f14])).
% 2.76/0.75  fof(f14,negated_conjecture,(
% 2.76/0.75    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.76/0.75    inference(negated_conjecture,[],[f13])).
% 2.76/0.75  fof(f13,conjecture,(
% 2.76/0.75    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 2.76/0.75  fof(f3250,plain,(
% 2.76/0.75    r2_hidden(sK0,sK2)),
% 2.76/0.75    inference(subsumption_resolution,[],[f3249,f22])).
% 2.76/0.75  fof(f22,plain,(
% 2.76/0.75    ~r2_hidden(sK1,sK2)),
% 2.76/0.75    inference(cnf_transformation,[],[f20])).
% 2.76/0.75  fof(f3249,plain,(
% 2.76/0.75    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 2.76/0.75    inference(resolution,[],[f3100,f35])).
% 2.76/0.75  fof(f35,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f18])).
% 2.76/0.75  fof(f18,plain,(
% 2.76/0.75    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f12])).
% 2.76/0.75  fof(f12,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 2.76/0.75  fof(f3100,plain,(
% 2.76/0.75    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.76/0.75    inference(trivial_inequality_removal,[],[f3099])).
% 2.76/0.75  fof(f3099,plain,(
% 2.76/0.75    sK2 != sK2 | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.76/0.75    inference(superposition,[],[f23,f2881])).
% 2.76/0.75  fof(f2881,plain,(
% 2.76/0.75    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = X3 | ~r1_xboole_0(X4,X3)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f2859,f48])).
% 2.76/0.75  fof(f48,plain,(
% 2.76/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.75    inference(forward_demodulation,[],[f47,f36])).
% 2.76/0.75  fof(f36,plain,(
% 2.76/0.75    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.75    inference(superposition,[],[f27,f24])).
% 2.76/0.75  fof(f24,plain,(
% 2.76/0.75    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f4])).
% 2.76/0.75  fof(f4,axiom,(
% 2.76/0.75    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.76/0.75  fof(f27,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f3])).
% 2.76/0.75  fof(f3,axiom,(
% 2.76/0.75    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.76/0.75  fof(f47,plain,(
% 2.76/0.75    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f45,f36])).
% 2.76/0.75  fof(f45,plain,(
% 2.76/0.75    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 2.76/0.75    inference(superposition,[],[f31,f24])).
% 2.76/0.75  fof(f31,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f7])).
% 2.76/0.75  fof(f7,axiom,(
% 2.76/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.76/0.75  fof(f2859,plain,(
% 2.76/0.75    ( ! [X4,X3] : (k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,X4) | ~r1_xboole_0(X4,X3)) )),
% 2.76/0.75    inference(superposition,[],[f30,f2777])).
% 2.76/0.75  fof(f2777,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f2734,f69])).
% 2.76/0.75  fof(f69,plain,(
% 2.76/0.75    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f68,f24])).
% 2.76/0.75  fof(f68,plain,(
% 2.76/0.75    ( ! [X6] : (k3_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,X6)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f59,f36])).
% 2.76/0.75  fof(f59,plain,(
% 2.76/0.75    ( ! [X6] : (k3_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k2_xboole_0(X6,k1_xboole_0))) )),
% 2.76/0.75    inference(superposition,[],[f32,f48])).
% 2.76/0.75  fof(f32,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f8])).
% 2.76/0.75  fof(f8,axiom,(
% 2.76/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.76/0.75  fof(f2734,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k5_xboole_0(X0,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(superposition,[],[f2088,f33])).
% 2.76/0.75  fof(f33,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f17])).
% 2.76/0.75  fof(f17,plain,(
% 2.76/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f15])).
% 2.76/0.75  fof(f15,plain,(
% 2.76/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.76/0.75    inference(unused_predicate_definition_removal,[],[f5])).
% 2.76/0.75  fof(f5,axiom,(
% 2.76/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.76/0.75  fof(f2088,plain,(
% 2.76/0.75    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X2,k4_xboole_0(X2,X1))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f2031,f444])).
% 2.76/0.75  fof(f444,plain,(
% 2.76/0.75    ( ! [X19,X20] : (k5_xboole_0(X20,k2_xboole_0(X19,X20)) = k4_xboole_0(X19,X20)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f422,f30])).
% 2.76/0.75  fof(f422,plain,(
% 2.76/0.75    ( ! [X19,X20] : (k5_xboole_0(X20,k2_xboole_0(X19,X20)) = k5_xboole_0(X19,k3_xboole_0(X19,X20))) )),
% 2.76/0.75    inference(superposition,[],[f113,f81])).
% 2.76/0.75  fof(f81,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 2.76/0.75    inference(superposition,[],[f34,f32])).
% 2.76/0.75  fof(f34,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f6])).
% 2.76/0.75  fof(f6,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.76/0.75  fof(f113,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.76/0.75    inference(forward_demodulation,[],[f109,f50])).
% 2.76/0.75  fof(f50,plain,(
% 2.76/0.75    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.76/0.75    inference(superposition,[],[f48,f26])).
% 2.76/0.75  fof(f26,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f1])).
% 2.76/0.75  fof(f1,axiom,(
% 2.76/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.76/0.75  fof(f109,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(superposition,[],[f34,f69])).
% 2.76/0.75  fof(f2031,plain,(
% 2.76/0.75    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))) )),
% 2.76/0.75    inference(superposition,[],[f176,f116])).
% 2.76/0.75  fof(f116,plain,(
% 2.76/0.75    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 2.76/0.75    inference(superposition,[],[f37,f28])).
% 2.76/0.75  fof(f28,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f11])).
% 2.76/0.75  fof(f11,axiom,(
% 2.76/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.76/0.75  fof(f37,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 2.76/0.75    inference(superposition,[],[f28,f25])).
% 2.76/0.75  fof(f25,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f9])).
% 2.76/0.75  fof(f9,axiom,(
% 2.76/0.75    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.76/0.75  fof(f176,plain,(
% 2.76/0.75    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k2_xboole_0(X4,X3)))) )),
% 2.76/0.75    inference(superposition,[],[f56,f34])).
% 2.76/0.75  fof(f56,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(superposition,[],[f32,f26])).
% 2.76/0.75  fof(f30,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f2])).
% 2.76/0.75  fof(f2,axiom,(
% 2.76/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.76/0.75  fof(f23,plain,(
% 2.76/0.75    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.76/0.75    inference(cnf_transformation,[],[f20])).
% 2.76/0.75  % SZS output end Proof for theBenchmark
% 2.76/0.75  % (27420)------------------------------
% 2.76/0.75  % (27420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.75  % (27420)Termination reason: Refutation
% 2.76/0.75  
% 2.76/0.75  % (27420)Memory used [KB]: 6140
% 2.76/0.75  % (27420)Time elapsed: 0.327 s
% 2.76/0.75  % (27420)------------------------------
% 2.76/0.75  % (27420)------------------------------
% 2.76/0.75  % (27416)Success in time 0.387 s
%------------------------------------------------------------------------------
