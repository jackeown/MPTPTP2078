%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  62 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 112 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f36,f41])).

fof(f41,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f35,f27,f38])).

fof(f38,plain,
    ( spl1_3
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f27,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(backward_demodulation,[],[f32,f33])).

fof(f33,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(resolution,[],[f32,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f32,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_2 ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(resolution,[],[f19,f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f36,plain,
    ( spl1_1
    | ~ spl1_2 ),
    inference(avatar_contradiction_clause,[],[f34])).

fof(f34,plain,
    ( $false
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f24,f33])).

fof(f24,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f30,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f15,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f25,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f22])).

fof(f14,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:20:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (22138)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (22138)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f25,f30,f36,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl1_3 | ~spl1_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f27,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl1_3 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl1_2),
% 0.21/0.49    inference(backward_demodulation,[],[f32,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_2),
% 0.21/0.49    inference(resolution,[],[f32,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k8_relat_1(X0,k1_xboole_0),k1_xboole_0)) ) | ~spl1_2),
% 0.21/0.49    inference(resolution,[],[f31,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f27])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.21/0.49    inference(resolution,[],[f19,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    spl1_1 | ~spl1_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    $false | (spl1_1 | ~spl1_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f24,f33])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    spl1_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f27])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(definition_unfolding,[],[f15,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~spl1_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f22])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22138)------------------------------
% 0.21/0.49  % (22138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22138)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22138)Memory used [KB]: 6012
% 0.21/0.49  % (22138)Time elapsed: 0.070 s
% 0.21/0.49  % (22138)------------------------------
% 0.21/0.49  % (22138)------------------------------
% 0.21/0.49  % (22127)Success in time 0.131 s
%------------------------------------------------------------------------------
