%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   83 ( 175 expanded)
%              Number of equality atoms :   27 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f48,f52])).

fof(f52,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f16,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f50,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,sK2))
    | spl3_2 ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f39,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f44,f35])).

fof(f35,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (11267)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f20,f28,f28])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f40,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f37,f33])).

fof(f17,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (11257)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (11258)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (11259)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (11260)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (11275)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (11276)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (11264)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (11259)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % (11264)Refutation not found, incomplete strategy% (11264)------------------------------
% 1.22/0.52  % (11264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (11264)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (11264)Memory used [KB]: 10618
% 1.22/0.52  % (11264)Time elapsed: 0.110 s
% 1.22/0.52  % (11264)------------------------------
% 1.22/0.52  % (11264)------------------------------
% 1.22/0.52  % (11266)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f53,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(avatar_sat_refutation,[],[f40,f48,f52])).
% 1.22/0.52  fof(f52,plain,(
% 1.22/0.52    spl3_2),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f51])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    $false | spl3_2),
% 1.22/0.52    inference(resolution,[],[f50,f29])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.22/0.52    inference(definition_unfolding,[],[f16,f28])).
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f18,f27])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f19,f26])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f22,f25])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    (~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.22/0.52    inference(ennf_transformation,[],[f9])).
% 1.22/0.52  fof(f9,negated_conjecture,(
% 1.22/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.22/0.52    inference(negated_conjecture,[],[f8])).
% 1.22/0.52  fof(f8,conjecture,(
% 1.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.22/0.52  fof(f50,plain,(
% 1.22/0.52    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(X0,sK2))) ) | spl3_2),
% 1.22/0.52    inference(resolution,[],[f39,f24])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.22/0.52    inference(ennf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    ~r2_hidden(k2_mcart_1(sK0),sK2) | spl3_2),
% 1.22/0.52    inference(avatar_component_clause,[],[f37])).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    spl3_2 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.22/0.52  fof(f48,plain,(
% 1.22/0.52    spl3_1),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f47])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    $false | spl3_1),
% 1.22/0.52    inference(subsumption_resolution,[],[f44,f35])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    sK1 != k1_mcart_1(sK0) | spl3_1),
% 1.22/0.52    inference(avatar_component_clause,[],[f33])).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    spl3_1 <=> sK1 = k1_mcart_1(sK0)),
% 1.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.22/0.52  fof(f44,plain,(
% 1.22/0.52    sK1 = k1_mcart_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f42,f29])).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.22/0.52    inference(resolution,[],[f41,f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1) )),
% 1.22/0.52    inference(resolution,[],[f30,f31])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.22/0.52    inference(definition_unfolding,[],[f21,f28])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f12])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  % (11267)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1) )),
% 1.22/0.52    inference(definition_unfolding,[],[f20,f28,f28])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.22/0.52    inference(ennf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ~spl3_1 | ~spl3_2),
% 1.22/0.52    inference(avatar_split_clause,[],[f17,f37,f33])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (11259)------------------------------
% 1.22/0.52  % (11259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (11259)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (11259)Memory used [KB]: 10618
% 1.22/0.52  % (11259)Time elapsed: 0.110 s
% 1.22/0.52  % (11259)------------------------------
% 1.22/0.52  % (11259)------------------------------
% 1.22/0.52  % (11278)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (11267)Refutation not found, incomplete strategy% (11267)------------------------------
% 1.22/0.52  % (11267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (11255)Success in time 0.159 s
%------------------------------------------------------------------------------
