%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 (  81 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f22,f26,f30,f36,f40])).

fof(f40,plain,
    ( spl2_1
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl2_1
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( sK0 != sK0
    | spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f17,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f17,plain,
    ( sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl2_1
  <=> sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f36,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f32,f28,f24,f20,f34])).

fof(f20,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f24,plain,
    ( spl2_3
  <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f28,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f32,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f31,f25])).

fof(f25,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f31,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = X0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f29,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f28])).

fof(f30,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f28])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f26,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f22,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f11,f20])).

fof(f11,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f18,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f10,f15])).

fof(f10,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0
   => sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:17:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (29158)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.42  % (29159)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (29159)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f18,f22,f26,f30,f36,f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl2_1 | ~spl2_5),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    $false | (spl2_1 | ~spl2_5)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    sK0 != sK0 | (spl2_1 | ~spl2_5)),
% 0.22/0.43    inference(superposition,[],[f17,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl2_5 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    spl2_1 <=> sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl2_5 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f32,f28,f24,f20,f34])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    spl2_2 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl2_3 <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl2_4 <=> ! [X1,X0] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.22/0.43    inference(forward_demodulation,[],[f31,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) ) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f24])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) ) | (~spl2_2 | ~spl2_4)),
% 0.22/0.43    inference(resolution,[],[f29,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f20])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) ) | ~spl2_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f28])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f28])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f12,f24])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f11,f20])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f10,f15])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 => sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (29159)------------------------------
% 0.22/0.43  % (29159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (29159)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (29159)Memory used [KB]: 6012
% 0.22/0.43  % (29159)Time elapsed: 0.004 s
% 0.22/0.43  % (29159)------------------------------
% 0.22/0.43  % (29159)------------------------------
% 0.22/0.44  % (29148)Success in time 0.074 s
%------------------------------------------------------------------------------
