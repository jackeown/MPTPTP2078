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
% DateTime   : Thu Dec  3 12:40:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 117 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f45,f57,f69])).

fof(f69,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f61,f37])).

fof(f37,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_2
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl2_4 ),
    inference(superposition,[],[f25,f56])).

fof(f56,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_4
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f48,f42,f54])).

fof(f42,plain,
    ( spl2_3
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f44,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f39,f30,f42])).

fof(f30,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f32,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f38,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f15,f23,f19,f23])).

fof(f15,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (28407)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.42  % (28407)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f33,f38,f45,f57,f69])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl2_2 | ~spl2_4),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    $false | (spl2_2 | ~spl2_4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f61,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl2_2 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl2_4),
% 0.20/0.42    inference(superposition,[],[f25,f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    spl2_4 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f17,f19,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl2_4 | ~spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f48,f42,f54])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_3 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | ~spl2_3),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f44,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.42    inference(definition_unfolding,[],[f20,f19])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f42])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl2_3 | ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f39,f30,f42])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl2_1),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f32,f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f22,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f16,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f35])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.42    inference(definition_unfolding,[],[f15,f23,f19,f23])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f30])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    r2_hidden(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (28407)------------------------------
% 0.20/0.42  % (28407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (28407)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (28407)Memory used [KB]: 10618
% 0.20/0.42  % (28407)Time elapsed: 0.005 s
% 0.20/0.42  % (28407)------------------------------
% 0.20/0.42  % (28407)------------------------------
% 0.20/0.42  % (28391)Success in time 0.069 s
%------------------------------------------------------------------------------
