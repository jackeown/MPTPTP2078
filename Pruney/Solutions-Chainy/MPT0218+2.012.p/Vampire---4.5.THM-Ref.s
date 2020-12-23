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
% DateTime   : Thu Dec  3 12:35:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  70 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f42])).

fof(f42,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f30,f40])).

fof(f40,plain,
    ( ! [X2,X0,X1] : r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f34,f38])).

fof(f38,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_3
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f34,plain,
    ( ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f30,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f20,f21,f16,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f33])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f28])).

fof(f25,plain,(
    ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f13,f23,f16])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:17:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (12016)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (12020)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (12016)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f31,f35,f39,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    $false | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f30,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.47    inference(superposition,[],[f34,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))))) ) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl2_3 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    spl2_2 <=> ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1)) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl2_1 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f37])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f19,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f21,f16,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f18,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f33])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f15,f21])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f28])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1))),
% 0.22/0.47    inference(definition_unfolding,[],[f13,f23,f16])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f14,f16])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (12016)------------------------------
% 0.22/0.47  % (12016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12016)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (12016)Memory used [KB]: 6012
% 0.22/0.47  % (12016)Time elapsed: 0.062 s
% 0.22/0.47  % (12016)------------------------------
% 0.22/0.47  % (12016)------------------------------
% 0.22/0.47  % (12008)Success in time 0.103 s
%------------------------------------------------------------------------------
