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
% DateTime   : Thu Dec  3 12:30:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  77 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22,f27,f31])).

fof(f31,plain,
    ( ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f29,f13])).

fof(f13,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f29,plain,
    ( r2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f16,f26])).

fof(f26,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f16,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl1_1
  <=> r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f27,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f23,f20,f25])).

fof(f20,plain,
    ( spl1_2
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f23,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_2 ),
    inference(resolution,[],[f21,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f21,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f22,plain,
    ( spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f15,f20])).

fof(f18,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(resolution,[],[f16,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f9,f15])).

fof(f9,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (27177)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (27177)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f17,f22,f27,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ~spl1_1 | ~spl1_3),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    $false | (~spl1_1 | ~spl1_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f29,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.22/0.47    inference(equality_resolution,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | X0 != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    r2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl1_1 | ~spl1_3)),
% 0.22/0.47    inference(superposition,[],[f16,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | ~spl1_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    spl1_3 <=> k1_xboole_0 = sK0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    r2_xboole_0(sK0,k1_xboole_0) | ~spl1_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    spl1_1 <=> r2_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    spl1_3 | ~spl1_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f20,f25])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    spl1_2 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | ~spl1_2),
% 0.22/0.47    inference(resolution,[],[f21,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    r1_tarski(sK0,k1_xboole_0) | ~spl1_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f20])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    spl1_2 | ~spl1_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f15,f20])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    r1_tarski(sK0,k1_xboole_0) | ~spl1_1),
% 0.22/0.47    inference(resolution,[],[f16,f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    spl1_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f9,f15])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    r2_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0] : r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    inference(negated_conjecture,[],[f3])).
% 0.22/0.47  fof(f3,conjecture,(
% 0.22/0.47    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (27177)------------------------------
% 0.22/0.47  % (27177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (27177)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (27177)Memory used [KB]: 6140
% 0.22/0.47  % (27177)Time elapsed: 0.061 s
% 0.22/0.47  % (27177)------------------------------
% 0.22/0.47  % (27177)------------------------------
% 0.22/0.48  % (27176)Success in time 0.112 s
%------------------------------------------------------------------------------
