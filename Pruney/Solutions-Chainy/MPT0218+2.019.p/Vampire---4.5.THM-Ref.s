%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 109 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 ( 126 expanded)
%              Number of equality atoms :   30 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f51,f54])).

fof(f54,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f46,f52])).

fof(f52,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f41,f50])).

fof(f50,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_3
  <=> ! [X1,X3,X5,X0,X2,X4] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f41,plain,
    ( ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_1
  <=> ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f49])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
    inference(definition_unfolding,[],[f27,f30,f29,f31,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f47,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f44])).

fof(f36,plain,(
    ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f17,f35,f34])).

fof(f17,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f37,f40])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f19,f29])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:57:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.45  % (17329)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.45  % (17329)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f42,f47,f51,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ~spl2_1 | spl2_2 | ~spl2_3),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    $false | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.22/0.45    inference(subsumption_resolution,[],[f46,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) ) | (~spl2_1 | ~spl2_3)),
% 0.22/0.45    inference(superposition,[],[f41,f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))))) ) | ~spl2_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl2_3 <=> ! [X1,X3,X5,X0,X2,X4] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ) | ~spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl2_1 <=> ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl2_2 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f38,f49])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f27,f30,f29,f31,f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f18,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f20,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f23,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f24,f31])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f25,f30])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f22,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f26,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ~spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f36,f44])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.22/0.45    inference(definition_unfolding,[],[f17,f35,f34])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.45    inference(negated_conjecture,[],[f12])).
% 0.22/0.45  fof(f12,conjecture,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f37,f40])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f19,f29])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (17329)------------------------------
% 0.22/0.45  % (17329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (17329)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (17329)Memory used [KB]: 6140
% 0.22/0.45  % (17329)Time elapsed: 0.006 s
% 0.22/0.45  % (17329)------------------------------
% 0.22/0.45  % (17329)------------------------------
% 0.22/0.45  % (17321)Success in time 0.083 s
%------------------------------------------------------------------------------
