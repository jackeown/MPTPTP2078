%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:41 EST 2020

% Result     : Theorem 4.06s
% Output     : Refutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 (  97 expanded)
%              Number of equality atoms :   42 (  70 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5916,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f37,f5829])).

fof(f5829,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f5828])).

fof(f5828,plain,
    ( $false
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f5827])).

fof(f5827,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f5826,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f22,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f5826,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f5825,f836])).

fof(f836,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f104,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f104,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(k2_xboole_0(X3,X5),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f23,f17])).

fof(f5825,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | spl3_2 ),
    inference(forward_demodulation,[],[f5824,f4351])).

fof(f4351,plain,(
    ! [X92,X90,X93,X91] : k2_xboole_0(k3_xboole_0(X90,X91),k3_xboole_0(k2_xboole_0(X90,X92),X93)) = k3_xboole_0(k2_xboole_0(X90,X92),k2_xboole_0(X93,k3_xboole_0(X90,X91))) ),
    inference(superposition,[],[f100,f129])).

fof(f129,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,X8) = k2_xboole_0(k3_xboole_0(X6,X7),k2_xboole_0(X6,X8)) ),
    inference(superposition,[],[f21,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5824,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f5701,f662])).

fof(f662,plain,(
    ! [X43,X41,X44,X42] : k3_xboole_0(k2_xboole_0(X42,X43),k3_xboole_0(X44,k2_xboole_0(X41,X42))) = k3_xboole_0(X44,k2_xboole_0(X42,k3_xboole_0(X41,X43))) ),
    inference(superposition,[],[f53,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[],[f23,f18])).

fof(f53,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X5,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f20,f17])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f5701,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f36,f270])).

fof(f270,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X8,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X7,X8),X6) ),
    inference(superposition,[],[f53,f17])).

fof(f36,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) = k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f32,f26,f34])).

fof(f26,plain,
    ( spl3_1
  <=> k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f32,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f31,f17])).

fof(f31,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK2,sK0),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f30,f18])).

fof(f30,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f28,f18])).

fof(f28,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (29864)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (29865)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (29859)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.47  % (29861)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.47  % (29866)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.47  % (29863)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.47  % (29862)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.47  % (29860)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.47  % (29870)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.47  % (29868)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.47  % (29869)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.48  % (29867)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 4.06/0.86  % (29860)Refutation found. Thanks to Tanya!
% 4.06/0.86  % SZS status Theorem for theBenchmark
% 4.06/0.86  % SZS output start Proof for theBenchmark
% 4.06/0.86  fof(f5916,plain,(
% 4.06/0.86    $false),
% 4.06/0.86    inference(avatar_sat_refutation,[],[f29,f37,f5829])).
% 4.06/0.86  fof(f5829,plain,(
% 4.06/0.86    spl3_2),
% 4.06/0.86    inference(avatar_contradiction_clause,[],[f5828])).
% 4.06/0.86  fof(f5828,plain,(
% 4.06/0.86    $false | spl3_2),
% 4.06/0.86    inference(trivial_inequality_removal,[],[f5827])).
% 4.06/0.86  fof(f5827,plain,(
% 4.06/0.86    k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) | spl3_2),
% 4.06/0.86    inference(forward_demodulation,[],[f5826,f81])).
% 4.06/0.86  fof(f81,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 4.06/0.86    inference(superposition,[],[f22,f17])).
% 4.06/0.86  fof(f17,plain,(
% 4.06/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.06/0.86    inference(cnf_transformation,[],[f2])).
% 4.06/0.86  fof(f2,axiom,(
% 4.06/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.06/0.86  fof(f22,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 4.06/0.86    inference(cnf_transformation,[],[f7])).
% 4.06/0.86  fof(f7,axiom,(
% 4.06/0.86    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 4.06/0.86  fof(f5826,plain,(
% 4.06/0.86    k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) | spl3_2),
% 4.06/0.86    inference(forward_demodulation,[],[f5825,f836])).
% 4.06/0.86  fof(f836,plain,(
% 4.06/0.86    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,X4))) )),
% 4.06/0.86    inference(superposition,[],[f104,f23])).
% 4.06/0.86  fof(f23,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 4.06/0.86    inference(cnf_transformation,[],[f8])).
% 4.06/0.86  fof(f8,axiom,(
% 4.06/0.86    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 4.06/0.86  fof(f104,plain,(
% 4.06/0.86    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(k2_xboole_0(X3,X5),k2_xboole_0(X3,X4))) )),
% 4.06/0.86    inference(superposition,[],[f23,f17])).
% 4.06/0.86  fof(f5825,plain,(
% 4.06/0.86    k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) | spl3_2),
% 4.06/0.86    inference(forward_demodulation,[],[f5824,f4351])).
% 4.06/0.86  fof(f4351,plain,(
% 4.06/0.86    ( ! [X92,X90,X93,X91] : (k2_xboole_0(k3_xboole_0(X90,X91),k3_xboole_0(k2_xboole_0(X90,X92),X93)) = k3_xboole_0(k2_xboole_0(X90,X92),k2_xboole_0(X93,k3_xboole_0(X90,X91)))) )),
% 4.06/0.86    inference(superposition,[],[f100,f129])).
% 4.06/0.86  fof(f129,plain,(
% 4.06/0.86    ( ! [X6,X8,X7] : (k2_xboole_0(X6,X8) = k2_xboole_0(k3_xboole_0(X6,X7),k2_xboole_0(X6,X8))) )),
% 4.06/0.86    inference(superposition,[],[f21,f40])).
% 4.06/0.86  fof(f40,plain,(
% 4.06/0.86    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 4.06/0.86    inference(resolution,[],[f19,f16])).
% 4.06/0.86  fof(f16,plain,(
% 4.06/0.86    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.06/0.86    inference(cnf_transformation,[],[f6])).
% 4.06/0.86  fof(f6,axiom,(
% 4.06/0.86    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.06/0.86  fof(f19,plain,(
% 4.06/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.06/0.86    inference(cnf_transformation,[],[f13])).
% 4.06/0.86  fof(f13,plain,(
% 4.06/0.86    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.06/0.86    inference(ennf_transformation,[],[f4])).
% 4.06/0.86  fof(f4,axiom,(
% 4.06/0.86    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.06/0.86  fof(f21,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.06/0.86    inference(cnf_transformation,[],[f9])).
% 4.06/0.86  fof(f9,axiom,(
% 4.06/0.86    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.06/0.86  fof(f100,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X0))) )),
% 4.06/0.86    inference(superposition,[],[f23,f18])).
% 4.06/0.86  fof(f18,plain,(
% 4.06/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.06/0.86    inference(cnf_transformation,[],[f1])).
% 4.06/0.86  fof(f1,axiom,(
% 4.06/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.06/0.86  fof(f5824,plain,(
% 4.06/0.86    k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | spl3_2),
% 4.06/0.86    inference(forward_demodulation,[],[f5701,f662])).
% 4.06/0.86  fof(f662,plain,(
% 4.06/0.86    ( ! [X43,X41,X44,X42] : (k3_xboole_0(k2_xboole_0(X42,X43),k3_xboole_0(X44,k2_xboole_0(X41,X42))) = k3_xboole_0(X44,k2_xboole_0(X42,k3_xboole_0(X41,X43)))) )),
% 4.06/0.86    inference(superposition,[],[f53,f96])).
% 4.06/0.86  fof(f96,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2))) )),
% 4.06/0.86    inference(superposition,[],[f23,f18])).
% 4.06/0.86  fof(f53,plain,(
% 4.06/0.86    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X5,k3_xboole_0(X3,X4))) )),
% 4.06/0.86    inference(superposition,[],[f20,f17])).
% 4.06/0.86  fof(f20,plain,(
% 4.06/0.86    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 4.06/0.86    inference(cnf_transformation,[],[f5])).
% 4.06/0.86  fof(f5,axiom,(
% 4.06/0.86    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 4.06/0.86  fof(f5701,plain,(
% 4.06/0.86    k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) != k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,sK1))) | spl3_2),
% 4.06/0.86    inference(superposition,[],[f36,f270])).
% 4.06/0.86  fof(f270,plain,(
% 4.06/0.86    ( ! [X6,X8,X7] : (k3_xboole_0(X8,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X7,X8),X6)) )),
% 4.06/0.86    inference(superposition,[],[f53,f17])).
% 4.06/0.86  fof(f36,plain,(
% 4.06/0.86    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | spl3_2),
% 4.06/0.86    inference(avatar_component_clause,[],[f34])).
% 4.06/0.86  fof(f34,plain,(
% 4.06/0.86    spl3_2 <=> k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) = k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))),
% 4.06/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.06/0.86  fof(f37,plain,(
% 4.06/0.86    ~spl3_2 | spl3_1),
% 4.06/0.86    inference(avatar_split_clause,[],[f32,f26,f34])).
% 4.06/0.86  fof(f26,plain,(
% 4.06/0.86    spl3_1 <=> k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 4.06/0.86    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.06/0.86  fof(f32,plain,(
% 4.06/0.86    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | spl3_1),
% 4.06/0.86    inference(forward_demodulation,[],[f31,f17])).
% 4.06/0.86  fof(f31,plain,(
% 4.06/0.86    k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK2,sK0),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | spl3_1),
% 4.06/0.86    inference(forward_demodulation,[],[f30,f18])).
% 4.06/0.86  fof(f30,plain,(
% 4.06/0.86    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK2)) | spl3_1),
% 4.06/0.86    inference(forward_demodulation,[],[f28,f18])).
% 4.06/0.86  fof(f28,plain,(
% 4.06/0.86    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) | spl3_1),
% 4.06/0.86    inference(avatar_component_clause,[],[f26])).
% 4.06/0.86  fof(f29,plain,(
% 4.06/0.86    ~spl3_1),
% 4.06/0.86    inference(avatar_split_clause,[],[f15,f26])).
% 4.06/0.86  fof(f15,plain,(
% 4.06/0.86    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 4.06/0.86    inference(cnf_transformation,[],[f12])).
% 4.06/0.86  fof(f12,plain,(
% 4.06/0.86    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 4.06/0.86    inference(ennf_transformation,[],[f11])).
% 4.06/0.86  fof(f11,negated_conjecture,(
% 4.06/0.86    ~! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 4.06/0.86    inference(negated_conjecture,[],[f10])).
% 4.06/0.86  fof(f10,conjecture,(
% 4.06/0.86    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 4.06/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).
% 4.06/0.86  % SZS output end Proof for theBenchmark
% 4.06/0.86  % (29860)------------------------------
% 4.06/0.86  % (29860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.86  % (29860)Termination reason: Refutation
% 4.06/0.86  
% 4.06/0.86  % (29860)Memory used [KB]: 19317
% 4.06/0.86  % (29860)Time elapsed: 0.442 s
% 4.06/0.86  % (29860)------------------------------
% 4.06/0.86  % (29860)------------------------------
% 4.06/0.87  % (29856)Success in time 0.506 s
%------------------------------------------------------------------------------
