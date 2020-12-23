%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:35 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f30])).

fof(f30,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f29])).

fof(f29,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f14,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f27,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f25])).

fof(f20,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f12,f15,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:27:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (4215)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.12/0.41  % (4215)Refutation found. Thanks to Tanya!
% 0.12/0.41  % SZS status Theorem for theBenchmark
% 0.12/0.41  % SZS output start Proof for theBenchmark
% 0.12/0.41  fof(f31,plain,(
% 0.12/0.41    $false),
% 0.12/0.41    inference(avatar_sat_refutation,[],[f28,f30])).
% 0.12/0.41  fof(f30,plain,(
% 0.12/0.41    spl2_1),
% 0.12/0.41    inference(avatar_contradiction_clause,[],[f29])).
% 0.12/0.41  fof(f29,plain,(
% 0.12/0.41    $false | spl2_1),
% 0.12/0.41    inference(subsumption_resolution,[],[f27,f21])).
% 0.12/0.41  fof(f21,plain,(
% 0.12/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.12/0.41    inference(unit_resulting_resolution,[],[f14,f16])).
% 0.12/0.41  fof(f16,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.12/0.41    inference(cnf_transformation,[],[f9])).
% 0.12/0.41  fof(f9,plain,(
% 0.12/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.12/0.41    inference(ennf_transformation,[],[f1])).
% 0.12/0.41  fof(f1,axiom,(
% 0.12/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.12/0.41  fof(f14,plain,(
% 0.12/0.41    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.12/0.41    inference(cnf_transformation,[],[f2])).
% 0.12/0.41  fof(f2,axiom,(
% 0.12/0.41    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.12/0.41  fof(f27,plain,(
% 0.12/0.41    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl2_1),
% 0.12/0.41    inference(avatar_component_clause,[],[f25])).
% 0.12/0.41  fof(f25,plain,(
% 0.12/0.41    spl2_1 <=> k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.12/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.12/0.41  fof(f28,plain,(
% 0.12/0.41    ~spl2_1),
% 0.12/0.41    inference(avatar_split_clause,[],[f20,f25])).
% 0.12/0.41  fof(f20,plain,(
% 0.12/0.41    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.12/0.41    inference(definition_unfolding,[],[f12,f15,f18])).
% 0.12/0.41  fof(f18,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.12/0.41    inference(definition_unfolding,[],[f17,f15])).
% 0.12/0.41  fof(f17,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.12/0.41    inference(cnf_transformation,[],[f4])).
% 0.12/0.41  fof(f4,axiom,(
% 0.12/0.41    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.12/0.41  fof(f15,plain,(
% 0.12/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.12/0.41    inference(cnf_transformation,[],[f3])).
% 0.12/0.41  fof(f3,axiom,(
% 0.12/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.12/0.41  fof(f12,plain,(
% 0.12/0.41    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.12/0.41    inference(cnf_transformation,[],[f11])).
% 0.12/0.41  fof(f11,plain,(
% 0.12/0.41    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.12/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).
% 0.12/0.41  fof(f10,plain,(
% 0.12/0.41    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.12/0.41    introduced(choice_axiom,[])).
% 0.12/0.41  fof(f8,plain,(
% 0.12/0.41    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.12/0.41    inference(ennf_transformation,[],[f7])).
% 0.12/0.41  fof(f7,negated_conjecture,(
% 0.12/0.41    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.12/0.41    inference(negated_conjecture,[],[f6])).
% 0.12/0.41  fof(f6,conjecture,(
% 0.12/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.12/0.41  % SZS output end Proof for theBenchmark
% 0.12/0.41  % (4215)------------------------------
% 0.12/0.41  % (4215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (4215)Termination reason: Refutation
% 0.12/0.41  
% 0.12/0.41  % (4215)Memory used [KB]: 10618
% 0.12/0.41  % (4215)Time elapsed: 0.004 s
% 0.12/0.41  % (4215)------------------------------
% 0.12/0.41  % (4215)------------------------------
% 0.12/0.41  % (4199)Success in time 0.06 s
%------------------------------------------------------------------------------
