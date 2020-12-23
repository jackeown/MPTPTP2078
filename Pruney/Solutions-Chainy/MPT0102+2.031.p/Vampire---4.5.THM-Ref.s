%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  91 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 109 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f47,f175,f186])).

fof(f186,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f70,f174])).

fof(f174,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl2_4
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f33,f57])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f56,f16])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f22,f16])).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f175,plain,
    ( ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f170,f44,f172])).

fof(f44,plain,
    ( spl2_2
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f170,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_2 ),
    inference(forward_demodulation,[],[f153,f70])).

fof(f153,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))
    | spl2_2 ),
    inference(superposition,[],[f46,f34])).

fof(f34,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f46,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f32,f28,f44])).

fof(f28,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_1 ),
    inference(backward_demodulation,[],[f30,f22])).

fof(f30,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f28])).

fof(f24,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(definition_unfolding,[],[f15,f20,f23])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:27:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (24381)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.40  % (24390)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.40  % (24381)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f187,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(avatar_sat_refutation,[],[f31,f47,f175,f186])).
% 0.19/0.40  fof(f186,plain,(
% 0.19/0.40    spl2_4),
% 0.19/0.40    inference(avatar_contradiction_clause,[],[f182])).
% 0.19/0.40  fof(f182,plain,(
% 0.19/0.40    $false | spl2_4),
% 0.19/0.40    inference(unit_resulting_resolution,[],[f70,f174])).
% 0.19/0.40  fof(f174,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_4),
% 0.19/0.40    inference(avatar_component_clause,[],[f172])).
% 0.19/0.40  fof(f172,plain,(
% 0.19/0.40    spl2_4 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.40  fof(f70,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.19/0.40    inference(forward_demodulation,[],[f33,f57])).
% 0.19/0.40  fof(f57,plain,(
% 0.19/0.40    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.19/0.40    inference(forward_demodulation,[],[f56,f16])).
% 0.19/0.40  fof(f16,plain,(
% 0.19/0.40    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.19/0.40    inference(cnf_transformation,[],[f6])).
% 0.19/0.40  fof(f6,axiom,(
% 0.19/0.40    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.40  fof(f56,plain,(
% 0.19/0.40    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 0.19/0.40    inference(forward_demodulation,[],[f25,f26])).
% 0.19/0.40  fof(f26,plain,(
% 0.19/0.40    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.19/0.40    inference(definition_unfolding,[],[f18,f20])).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f4])).
% 0.19/0.40  fof(f4,axiom,(
% 0.19/0.40    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.19/0.40    inference(cnf_transformation,[],[f11])).
% 0.19/0.40  fof(f11,plain,(
% 0.19/0.40    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.40    inference(rectify,[],[f3])).
% 0.19/0.40  fof(f3,axiom,(
% 0.19/0.40    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 0.19/0.40    inference(definition_unfolding,[],[f17,f23])).
% 0.19/0.40  fof(f23,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.40    inference(definition_unfolding,[],[f21,f20])).
% 0.19/0.40  fof(f21,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f7])).
% 0.19/0.40  fof(f7,axiom,(
% 0.19/0.40    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.19/0.40  fof(f17,plain,(
% 0.19/0.40    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.19/0.40    inference(cnf_transformation,[],[f10])).
% 0.19/0.40  fof(f10,plain,(
% 0.19/0.40    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.40    inference(rectify,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.19/0.40  fof(f33,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.19/0.40    inference(superposition,[],[f22,f16])).
% 0.19/0.40  fof(f22,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f5])).
% 0.19/0.40  fof(f5,axiom,(
% 0.19/0.40    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.19/0.40  fof(f175,plain,(
% 0.19/0.40    ~spl2_4 | spl2_2),
% 0.19/0.40    inference(avatar_split_clause,[],[f170,f44,f172])).
% 0.19/0.40  fof(f44,plain,(
% 0.19/0.40    spl2_2 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.40  fof(f170,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_2),
% 0.19/0.40    inference(forward_demodulation,[],[f153,f70])).
% 0.19/0.40  fof(f153,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))) | spl2_2),
% 0.19/0.40    inference(superposition,[],[f46,f34])).
% 0.19/0.40  fof(f34,plain,(
% 0.19/0.40    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) )),
% 0.19/0.40    inference(superposition,[],[f22,f19])).
% 0.19/0.40  fof(f19,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f1])).
% 0.19/0.40  fof(f1,axiom,(
% 0.19/0.40    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.19/0.40  fof(f46,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_2),
% 0.19/0.40    inference(avatar_component_clause,[],[f44])).
% 0.19/0.40  fof(f47,plain,(
% 0.19/0.40    ~spl2_2 | spl2_1),
% 0.19/0.40    inference(avatar_split_clause,[],[f32,f28,f44])).
% 0.19/0.40  fof(f28,plain,(
% 0.19/0.40    spl2_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.40  fof(f32,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_1),
% 0.19/0.40    inference(backward_demodulation,[],[f30,f22])).
% 0.19/0.40  fof(f30,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_1),
% 0.19/0.40    inference(avatar_component_clause,[],[f28])).
% 0.19/0.40  fof(f31,plain,(
% 0.19/0.40    ~spl2_1),
% 0.19/0.40    inference(avatar_split_clause,[],[f24,f28])).
% 0.19/0.40  fof(f24,plain,(
% 0.19/0.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.19/0.40    inference(definition_unfolding,[],[f15,f20,f23])).
% 0.19/0.40  fof(f15,plain,(
% 0.19/0.40    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f14,plain,(
% 0.19/0.40    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.19/0.40  fof(f13,plain,(
% 0.19/0.40    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f12,plain,(
% 0.19/0.40    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.40    inference(ennf_transformation,[],[f9])).
% 0.19/0.40  fof(f9,negated_conjecture,(
% 0.19/0.40    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.40    inference(negated_conjecture,[],[f8])).
% 0.19/0.40  fof(f8,conjecture,(
% 0.19/0.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (24381)------------------------------
% 0.19/0.40  % (24381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (24381)Termination reason: Refutation
% 0.19/0.40  
% 0.19/0.40  % (24381)Memory used [KB]: 6140
% 0.19/0.40  % (24381)Time elapsed: 0.032 s
% 0.19/0.40  % (24381)------------------------------
% 0.19/0.40  % (24381)------------------------------
% 0.19/0.40  % (24374)Success in time 0.061 s
%------------------------------------------------------------------------------
