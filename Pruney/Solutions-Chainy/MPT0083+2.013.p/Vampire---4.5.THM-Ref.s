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
% DateTime   : Thu Dec  3 12:31:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 126 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 189 expanded)
%              Number of equality atoms :    9 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f38,f45,f115,f120])).

fof(f120,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f116,f93])).

fof(f93,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(sK0,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f78,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f78,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,X0),sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f72,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f52,f25])).

fof(f52,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f30,f24,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f67,f114,f22])).

fof(f114,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_6
  <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(backward_demodulation,[],[f56,f62])).

fof(f56,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X2) ),
    inference(superposition,[],[f24,f25])).

fof(f115,plain,
    ( ~ spl3_6
    | spl3_3 ),
    inference(avatar_split_clause,[],[f51,f42,f112])).

fof(f42,plain,
    ( spl3_3
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f44,f21])).

fof(f44,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f40,f35,f42])).

fof(f35,plain,
    ( spl3_2
  <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f39,f25])).

fof(f39,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f37,f25])).

fof(f37,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f38,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f35])).

fof(f23,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f16,f19,f19])).

fof(f16,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (23086)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.46  % (23078)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (23075)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (23084)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (23086)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f121,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f31,f38,f45,f115,f120])).
% 0.19/0.46  fof(f120,plain,(
% 0.19/0.46    ~spl3_1 | spl3_6),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f119])).
% 0.19/0.46  fof(f119,plain,(
% 0.19/0.46    $false | (~spl3_1 | spl3_6)),
% 0.19/0.46    inference(subsumption_resolution,[],[f116,f93])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(sK0,X0))) ) | ~spl3_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f78,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),sK1)) ) | ~spl3_1),
% 0.19/0.46    inference(forward_demodulation,[],[f72,f62])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.19/0.46    inference(superposition,[],[f26,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.46    inference(definition_unfolding,[],[f18,f19,f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.46    inference(definition_unfolding,[],[f20,f19])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))),sK1)) ) | ~spl3_1),
% 0.19/0.46    inference(superposition,[],[f52,f25])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK1)) ) | ~spl3_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f30,f24,f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f17,f19])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.46  fof(f116,plain,(
% 0.19/0.46    ~r1_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl3_6),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f67,f114,f22])).
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl3_6),
% 0.19/0.46    inference(avatar_component_clause,[],[f112])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    spl3_6 <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 0.19/0.46    inference(backward_demodulation,[],[f56,f62])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X2)) )),
% 0.19/0.46    inference(superposition,[],[f24,f25])).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    ~spl3_6 | spl3_3),
% 0.19/0.46    inference(avatar_split_clause,[],[f51,f42,f112])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    spl3_3 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl3_3),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f44,f21])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f42])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ~spl3_3 | spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f40,f35,f42])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    spl3_2 <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_2),
% 0.19/0.46    inference(forward_demodulation,[],[f39,f25])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_2),
% 0.19/0.46    inference(forward_demodulation,[],[f37,f25])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) | spl3_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f35])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ~spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f23,f35])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 0.19/0.46    inference(definition_unfolding,[],[f16,f19,f19])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.19/0.46    inference(negated_conjecture,[],[f7])).
% 0.19/0.46  fof(f7,conjecture,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f15,f28])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    r1_xboole_0(sK0,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (23086)------------------------------
% 0.19/0.46  % (23086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (23086)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (23086)Memory used [KB]: 10618
% 0.19/0.46  % (23086)Time elapsed: 0.060 s
% 0.19/0.46  % (23086)------------------------------
% 0.19/0.46  % (23086)------------------------------
% 0.19/0.47  % (23070)Success in time 0.112 s
%------------------------------------------------------------------------------
