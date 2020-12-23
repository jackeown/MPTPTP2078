%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:06 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 112 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :   77 ( 129 expanded)
%              Number of equality atoms :   57 ( 106 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f66,f3375])).

fof(f3375,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f3328])).

fof(f3328,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f65,f3271])).

fof(f3271,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f3270,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3270,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3219,f170])).

fof(f170,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f97,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f97,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X3) ),
    inference(superposition,[],[f86,f67])).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f34,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f86,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(forward_demodulation,[],[f36,f29])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3219,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f123,f3131])).

fof(f3131,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f3130,f21])).

fof(f3130,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k1_xboole_0),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f3129,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f3129,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2994,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f21])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2994,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f196,f20])).

fof(f196,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X2,X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),X1)))) ),
    inference(unit_resulting_resolution,[],[f23,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X0) = k5_xboole_0(k4_xboole_0(X2,X0),k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1)))) ) ),
    inference(forward_demodulation,[],[f164,f29])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X0),X1),k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X0),X1),k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f123,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f26,f32,f32])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f65,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f56,f39,f63])).

fof(f39,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f56,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_1 ),
    inference(superposition,[],[f41,f29])).

fof(f41,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f33,f39])).

fof(f33,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f32])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:42:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (17192)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.42  % (17181)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.44  % (17189)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.44  % (17184)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.44  % (17189)Refutation not found, incomplete strategy% (17189)------------------------------
% 0.19/0.44  % (17189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (17189)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (17189)Memory used [KB]: 10490
% 0.19/0.44  % (17189)Time elapsed: 0.069 s
% 0.19/0.44  % (17189)------------------------------
% 0.19/0.44  % (17189)------------------------------
% 0.19/0.45  % (17190)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.45  % (17191)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (17180)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (17186)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.46  % (17178)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (17179)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  % (17188)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.47  % (17182)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (17183)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.47  % (17194)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.48  % (17193)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.48  % (17187)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (17195)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.49  % (17185)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 2.81/0.75  % (17184)Refutation found. Thanks to Tanya!
% 2.81/0.75  % SZS status Theorem for theBenchmark
% 2.81/0.75  % SZS output start Proof for theBenchmark
% 2.81/0.75  fof(f3453,plain,(
% 2.81/0.75    $false),
% 2.81/0.75    inference(avatar_sat_refutation,[],[f42,f66,f3375])).
% 2.81/0.75  fof(f3375,plain,(
% 2.81/0.75    spl2_2),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f3328])).
% 2.81/0.75  fof(f3328,plain,(
% 2.81/0.75    $false | spl2_2),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f65,f3271])).
% 2.81/0.75  fof(f3271,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f3270,f21])).
% 2.81/0.75  fof(f21,plain,(
% 2.81/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f8])).
% 2.81/0.75  fof(f8,axiom,(
% 2.81/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.81/0.75  fof(f3270,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) )),
% 2.81/0.75    inference(forward_demodulation,[],[f3219,f170])).
% 2.81/0.75  fof(f170,plain,(
% 2.81/0.75    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 2.81/0.75    inference(superposition,[],[f97,f22])).
% 2.81/0.75  fof(f22,plain,(
% 2.81/0.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f3])).
% 2.81/0.75  fof(f3,axiom,(
% 2.81/0.75    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.81/0.75  fof(f97,plain,(
% 2.81/0.75    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X2),X3)) )),
% 2.81/0.75    inference(superposition,[],[f86,f67])).
% 2.81/0.75  fof(f67,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f34,f29])).
% 2.81/0.75  fof(f29,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f11])).
% 2.81/0.75  fof(f11,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.81/0.75  fof(f34,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 2.81/0.75    inference(definition_unfolding,[],[f24,f32])).
% 2.81/0.75  fof(f32,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.81/0.75    inference(definition_unfolding,[],[f28,f27])).
% 2.81/0.75  fof(f27,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f6])).
% 2.81/0.75  fof(f6,axiom,(
% 2.81/0.75    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.81/0.75  fof(f28,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f12])).
% 2.81/0.75  fof(f12,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.81/0.75  fof(f24,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f5])).
% 2.81/0.75  fof(f5,axiom,(
% 2.81/0.75    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.81/0.75  fof(f86,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f36,f29])).
% 2.81/0.75  fof(f36,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 2.81/0.75    inference(definition_unfolding,[],[f30,f32])).
% 2.81/0.75  fof(f30,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f4])).
% 2.81/0.75  fof(f4,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.81/0.75  fof(f3219,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0))) )),
% 2.81/0.75    inference(backward_demodulation,[],[f123,f3131])).
% 2.81/0.75  fof(f3131,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X0,X1)) = X1) )),
% 2.81/0.75    inference(forward_demodulation,[],[f3130,f21])).
% 2.81/0.75  fof(f3130,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k1_xboole_0),k4_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f3129,f20])).
% 2.81/0.75  fof(f20,plain,(
% 2.81/0.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f7])).
% 2.81/0.75  fof(f7,axiom,(
% 2.81/0.75    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.81/0.75  fof(f3129,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f2994,f45])).
% 2.81/0.75  fof(f45,plain,(
% 2.81/0.75    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.81/0.75    inference(superposition,[],[f25,f21])).
% 2.81/0.75  fof(f25,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f1])).
% 2.81/0.75  fof(f1,axiom,(
% 2.81/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.81/0.75  fof(f2994,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))),k4_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(superposition,[],[f196,f20])).
% 2.81/0.75  fof(f196,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X2,X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),X1))))) )),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f23,f165])).
% 2.81/0.75  fof(f165,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X0) = k5_xboole_0(k4_xboole_0(X2,X0),k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f164,f29])).
% 2.81/0.75  fof(f164,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X0),X1),k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X0) | ~r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(forward_demodulation,[],[f37,f29])).
% 2.81/0.75  fof(f37,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k4_xboole_0(X2,X0),X1),k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(k4_xboole_0(X2,X0),X1))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))),X0) | ~r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(definition_unfolding,[],[f31,f32,f32])).
% 2.81/0.75  fof(f31,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f16])).
% 2.81/0.75  fof(f16,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f10])).
% 2.81/0.75  fof(f10,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 2.81/0.75  fof(f23,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f9])).
% 2.81/0.75  fof(f9,axiom,(
% 2.81/0.75    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.81/0.75  fof(f123,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 2.81/0.75    inference(forward_demodulation,[],[f35,f29])).
% 2.81/0.75  fof(f35,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 2.81/0.75    inference(definition_unfolding,[],[f26,f32,f32])).
% 2.81/0.75  fof(f26,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f2])).
% 2.81/0.75  fof(f2,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.81/0.75  fof(f65,plain,(
% 2.81/0.75    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_2),
% 2.81/0.75    inference(avatar_component_clause,[],[f63])).
% 2.81/0.75  fof(f63,plain,(
% 2.81/0.75    spl2_2 <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.81/0.75  fof(f66,plain,(
% 2.81/0.75    ~spl2_2 | spl2_1),
% 2.81/0.75    inference(avatar_split_clause,[],[f56,f39,f63])).
% 2.81/0.75  fof(f39,plain,(
% 2.81/0.75    spl2_1 <=> k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.81/0.75  fof(f56,plain,(
% 2.81/0.75    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_1),
% 2.81/0.75    inference(superposition,[],[f41,f29])).
% 2.81/0.75  fof(f41,plain,(
% 2.81/0.75    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 2.81/0.75    inference(avatar_component_clause,[],[f39])).
% 2.81/0.75  fof(f42,plain,(
% 2.81/0.75    ~spl2_1),
% 2.81/0.75    inference(avatar_split_clause,[],[f33,f39])).
% 2.81/0.75  fof(f33,plain,(
% 2.81/0.75    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.81/0.75    inference(definition_unfolding,[],[f19,f32])).
% 2.81/0.75  fof(f19,plain,(
% 2.81/0.75    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.81/0.75    inference(cnf_transformation,[],[f18])).
% 2.81/0.75  fof(f18,plain,(
% 2.81/0.75    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.81/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 2.81/0.75  fof(f17,plain,(
% 2.81/0.75    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.81/0.75    introduced(choice_axiom,[])).
% 2.81/0.75  fof(f15,plain,(
% 2.81/0.75    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f14])).
% 2.81/0.75  fof(f14,negated_conjecture,(
% 2.81/0.75    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.75    inference(negated_conjecture,[],[f13])).
% 2.81/0.75  fof(f13,conjecture,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.81/0.75  % SZS output end Proof for theBenchmark
% 2.81/0.75  % (17184)------------------------------
% 2.81/0.75  % (17184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.75  % (17184)Termination reason: Refutation
% 2.81/0.75  
% 2.81/0.75  % (17184)Memory used [KB]: 13816
% 2.81/0.75  % (17184)Time elapsed: 0.323 s
% 2.81/0.75  % (17184)------------------------------
% 2.81/0.75  % (17184)------------------------------
% 2.81/0.75  % (17175)Success in time 0.408 s
%------------------------------------------------------------------------------
