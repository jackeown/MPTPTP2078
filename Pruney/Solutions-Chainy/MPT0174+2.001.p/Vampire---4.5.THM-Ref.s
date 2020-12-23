%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:59 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  45 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f30])).

fof(f30,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f29])).

fof(f29,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f27,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f27,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl4_1
  <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f28,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f25])).

fof(f21,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

fof(f20,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) ),
    inference(definition_unfolding,[],[f11,f17,f18])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)),k2_xboole_0(k1_enumset1(X4,X4,X4),k1_enumset1(X5,X6,X7))) ),
    inference(definition_unfolding,[],[f16,f17,f17])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:31:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (4995)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.13/0.42  % (4995)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f31,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f28,f30])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    spl4_1),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f29])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    $false | spl4_1),
% 0.13/0.42    inference(subsumption_resolution,[],[f27,f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) | spl4_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f25])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    spl4_1 <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ~spl4_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f21,f25])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.13/0.42    inference(forward_demodulation,[],[f20,f19])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f13,f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.13/0.42    inference(definition_unfolding,[],[f11,f17,f18])).
% 0.13/0.43  fof(f18,plain,(
% 0.13/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)),k2_xboole_0(k1_enumset1(X4,X4,X4),k1_enumset1(X5,X6,X7)))) )),
% 0.13/0.43    inference(definition_unfolding,[],[f16,f17,f17])).
% 0.13/0.43  fof(f16,plain,(
% 0.13/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.13/0.43    inference(cnf_transformation,[],[f2])).
% 0.13/0.43  fof(f2,axiom,(
% 0.13/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.13/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 0.13/0.43  fof(f17,plain,(
% 0.13/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) )),
% 0.13/0.43    inference(definition_unfolding,[],[f14,f15])).
% 0.13/0.43  fof(f14,plain,(
% 0.13/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.13/0.43    inference(cnf_transformation,[],[f4])).
% 0.13/0.43  fof(f4,axiom,(
% 0.13/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.13/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.13/0.43  fof(f11,plain,(
% 0.13/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3)),
% 0.13/0.43    inference(cnf_transformation,[],[f10])).
% 0.13/0.43  fof(f10,plain,(
% 0.13/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3)),
% 0.13/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.13/0.43  fof(f9,plain,(
% 0.13/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3)),
% 0.13/0.43    introduced(choice_axiom,[])).
% 0.13/0.43  fof(f8,plain,(
% 0.13/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)),
% 0.13/0.43    inference(ennf_transformation,[],[f7])).
% 0.13/0.43  fof(f7,negated_conjecture,(
% 0.13/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)),
% 0.13/0.43    inference(negated_conjecture,[],[f6])).
% 0.13/0.43  fof(f6,conjecture,(
% 0.13/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)),
% 0.13/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_enumset1)).
% 0.13/0.43  % SZS output end Proof for theBenchmark
% 0.13/0.43  % (4995)------------------------------
% 0.13/0.43  % (4995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.43  % (4995)Termination reason: Refutation
% 0.13/0.43  
% 0.13/0.43  % (4995)Memory used [KB]: 10618
% 0.13/0.43  % (4995)Time elapsed: 0.008 s
% 0.13/0.43  % (4995)------------------------------
% 0.13/0.43  % (4995)------------------------------
% 0.13/0.43  % (4987)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.13/0.43  % (4979)Success in time 0.07 s
%------------------------------------------------------------------------------
