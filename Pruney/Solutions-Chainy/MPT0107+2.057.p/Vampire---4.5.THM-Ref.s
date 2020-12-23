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
% DateTime   : Thu Dec  3 12:32:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 218 expanded)
%              Number of leaves         :   11 (  73 expanded)
%              Depth                    :   19
%              Number of atoms          :   60 ( 224 expanded)
%              Number of equality atoms :   52 ( 215 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f412])).

fof(f412,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f410,f103])).

fof(f103,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f27,f100])).

fof(f100,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f93,f17])).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f93,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f22,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f17,f27])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f25,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f15,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f410,plain,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl2_1 ),
    inference(backward_demodulation,[],[f37,f409])).

fof(f409,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f408,f90])).

fof(f90,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f33,f22])).

fof(f408,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f385,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(forward_demodulation,[],[f59,f22])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f385,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)) ),
    inference(superposition,[],[f68,f126])).

fof(f126,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f125,f105])).

fof(f105,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f88,f103])).

fof(f88,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f87,f16])).

fof(f87,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f76,f33])).

fof(f76,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k1_xboole_0) ),
    inference(superposition,[],[f29,f17])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(backward_demodulation,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f125,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f118,f22])).

fof(f118,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f107,f26])).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f29,f105])).

fof(f37,plain,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f35])).

fof(f30,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    inference(backward_demodulation,[],[f28,f22])).

fof(f28,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(backward_demodulation,[],[f24,f26])).

fof(f24,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f14,f21,f18])).

fof(f14,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (1695)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (1691)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (1693)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (1688)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (1692)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (1701)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (1703)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (1690)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1687)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (1686)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (1697)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (1697)Refutation not found, incomplete strategy% (1697)------------------------------
% 0.21/0.49  % (1697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1697)Memory used [KB]: 10490
% 0.21/0.49  % (1697)Time elapsed: 0.082 s
% 0.21/0.49  % (1697)------------------------------
% 0.21/0.49  % (1697)------------------------------
% 0.21/0.49  % (1696)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (1700)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (1694)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (1702)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (1701)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f38,f412])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f411])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    $false | spl2_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f410,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(backward_demodulation,[],[f27,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f93,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.21/0.50    inference(superposition,[],[f22,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f17,f27])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.51    inference(backward_demodulation,[],[f25,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl2_1),
% 0.21/0.51    inference(backward_demodulation,[],[f37,f409])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f408,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 0.21/0.51    inference(superposition,[],[f33,f22])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f385,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f59,f22])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 0.21/0.51    inference(superposition,[],[f22,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1))) )),
% 0.21/0.51    inference(superposition,[],[f68,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f125,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.51    inference(backward_demodulation,[],[f88,f103])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f87,f16])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f76,f33])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f29,f17])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0)))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f23,f22])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f21])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))),k4_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f118,f22])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(superposition,[],[f107,f26])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f29,f105])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    spl2_1 <=> k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f35])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f28,f22])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f24,f26])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.21/0.51    inference(definition_unfolding,[],[f14,f21,f18])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (1701)------------------------------
% 0.21/0.51  % (1701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1701)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (1701)Memory used [KB]: 11001
% 0.21/0.51  % (1701)Time elapsed: 0.089 s
% 0.21/0.51  % (1701)------------------------------
% 0.21/0.51  % (1701)------------------------------
% 0.21/0.51  % (1685)Success in time 0.154 s
%------------------------------------------------------------------------------
