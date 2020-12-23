%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  83 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f39,f48])).

% (9419)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f48,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f42,f38])).

fof(f38,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_3
  <=> r1_tarski(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f20,f32])).

fof(f32,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK2,k1_tarski(sK1))),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK2,k1_tarski(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f39,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f34,f25,f36])).

fof(f25,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f27,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f30])).

fof(f23,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK2,k1_tarski(sK1))),sK2) ),
    inference(forward_demodulation,[],[f22,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f22,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f21,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f21,plain,(
    r1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2),sK2) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f13,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (9427)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (9427)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f28,f33,f39,f48])).
% 0.20/0.46  % (9419)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ~spl3_2 | spl3_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    $false | (~spl3_2 | spl3_3)),
% 0.20/0.46    inference(subsumption_resolution,[],[f42,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ~r1_tarski(k1_tarski(sK0),sK2) | spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl3_3 <=> r1_tarski(k1_tarski(sK0),sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    r1_tarski(k1_tarski(sK0),sK2) | ~spl3_2),
% 0.20/0.46    inference(resolution,[],[f20,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK2,k1_tarski(sK1))),sK2) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl3_2 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK2,k1_tarski(sK1))),sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ~spl3_3 | spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f34,f25,f36])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    spl3_1 <=> r2_hidden(sK0,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~r1_tarski(k1_tarski(sK0),sK2) | spl3_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f27,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK2) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f25])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f30])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(sK2,k1_tarski(sK1))),sK2)),
% 0.20/0.46    inference(forward_demodulation,[],[f22,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK2)),sK2)),
% 0.20/0.46    inference(backward_demodulation,[],[f21,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    r1_tarski(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2),sK2)),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f25])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (9427)------------------------------
% 0.20/0.46  % (9427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9427)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (9427)Memory used [KB]: 10618
% 0.20/0.46  % (9427)Time elapsed: 0.010 s
% 0.20/0.46  % (9427)------------------------------
% 0.20/0.46  % (9427)------------------------------
% 0.20/0.46  % (9412)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (9421)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (9413)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (9411)Success in time 0.109 s
%------------------------------------------------------------------------------
