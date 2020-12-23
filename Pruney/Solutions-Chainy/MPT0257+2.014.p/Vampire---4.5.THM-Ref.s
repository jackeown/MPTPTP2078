%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  33 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  56 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f34])).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl2_2 ),
    inference(global_subsumption,[],[f10,f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f26,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = k3_xboole_0(X1,k1_enumset1(X0,X0,X0)) ) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f12,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f26,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_2
  <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f10,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f27,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f11,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (19620)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.43  % (19637)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.43  % (19637)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f27,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    $false | spl2_2),
% 0.21/0.43    inference(global_subsumption,[],[f10,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~r2_hidden(sK0,sK1) | spl2_2),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f26,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k3_xboole_0(X1,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f14,f12,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    spl2_2 <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f24])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.43    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (19637)------------------------------
% 0.21/0.43  % (19637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19637)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (19637)Memory used [KB]: 10618
% 0.21/0.43  % (19637)Time elapsed: 0.045 s
% 0.21/0.43  % (19637)------------------------------
% 0.21/0.43  % (19637)------------------------------
% 0.21/0.44  % (19617)Success in time 0.083 s
%------------------------------------------------------------------------------
