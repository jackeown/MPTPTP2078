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
% DateTime   : Thu Dec  3 12:32:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 204 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :   72 ( 215 expanded)
%              Number of equality atoms :   60 ( 200 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f925,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f54,f879])).

fof(f879,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f853])).

fof(f853,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f53,f825])).

fof(f825,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f824,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f824,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f786,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f31,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f786,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f70,f550])).

fof(f550,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X15)) = X15 ),
    inference(forward_demodulation,[],[f549,f20])).

fof(f549,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X15)) = k4_xboole_0(X15,k1_xboole_0) ),
    inference(forward_demodulation,[],[f517,f42])).

fof(f517,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X15)) = k4_xboole_0(X15,k4_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X15))) ),
    inference(superposition,[],[f243,f121])).

fof(f121,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f112,f20])).

fof(f112,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f83,f42])).

fof(f83,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(forward_demodulation,[],[f82,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(forward_demodulation,[],[f33,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(forward_demodulation,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f27,f29,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f243,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f242,f19])).

fof(f242,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f241,f19])).

fof(f241,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f215,f117])).

fof(f117,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f116,f42])).

fof(f116,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f108,f20])).

fof(f108,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) ),
    inference(superposition,[],[f83,f42])).

% (14891)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f215,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0),k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(superposition,[],[f213,f42])).

fof(f213,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) ),
    inference(definition_unfolding,[],[f26,f22,f29])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f32,f24])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f21,f29,f29])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f53,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_2
  <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f54,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f46,f38,f51])).

fof(f38,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_1 ),
    inference(superposition,[],[f40,f24])).

% (14887)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f40,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f38])).

fof(f30,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f29])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (14888)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.46  % (14878)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (14880)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (14889)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (14883)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (14881)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (14877)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (14880)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (14874)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (14886)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (14875)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (14876)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (14884)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (14882)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f925,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f41,f54,f879])).
% 0.22/0.49  fof(f879,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f853])).
% 0.22/0.49  fof(f853,plain,(
% 0.22/0.49    $false | spl2_2),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f53,f825])).
% 0.22/0.49  fof(f825,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f824,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.49  fof(f824,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f786,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f31,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f18,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.49  fof(f786,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f70,f550])).
% 0.22/0.49  fof(f550,plain,(
% 0.22/0.49    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X15)) = X15) )),
% 0.22/0.49    inference(forward_demodulation,[],[f549,f20])).
% 0.22/0.49  fof(f549,plain,(
% 0.22/0.49    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X15)) = k4_xboole_0(X15,k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f517,f42])).
% 0.22/0.49  fof(f517,plain,(
% 0.22/0.49    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X15)) = k4_xboole_0(X15,k4_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X15)))) )),
% 0.22/0.49    inference(superposition,[],[f243,f121])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f112,f20])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.22/0.49    inference(superposition,[],[f83,f42])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f82,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f33,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f25,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f35,f24])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f27,f29,f22])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f242,f19])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f241,f19])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f215,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f116,f42])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f108,f20])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0))) )),
% 0.22/0.49    inference(superposition,[],[f83,f42])).
% 0.22/0.49  % (14891)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0),k4_xboole_0(k4_xboole_0(X2,X3),X2))) )),
% 0.22/0.49    inference(superposition,[],[f213,f42])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f34,f83])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f26,f22,f29])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f32,f24])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f21,f29,f29])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl2_2 <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~spl2_2 | spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f38,f51])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl2_1 <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_1),
% 0.22/0.49    inference(superposition,[],[f40,f24])).
% 0.22/0.49  % (14887)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f38])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.49    inference(definition_unfolding,[],[f17,f29])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (14880)------------------------------
% 0.22/0.49  % (14880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14880)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (14880)Memory used [KB]: 6652
% 0.22/0.49  % (14880)Time elapsed: 0.067 s
% 0.22/0.49  % (14880)------------------------------
% 0.22/0.49  % (14880)------------------------------
% 0.22/0.50  % (14873)Success in time 0.136 s
%------------------------------------------------------------------------------
