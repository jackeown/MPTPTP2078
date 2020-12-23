%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  97 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 159 expanded)
%              Number of equality atoms :   20 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f52,f73,f81,f90])).

fof(f90,plain,
    ( spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f88,f72])).

fof(f72,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_4
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f88,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f60,f80])).

fof(f80,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_5
  <=> sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f81,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f55,f49,f78])).

fof(f49,plain,
    ( spl2_3
  <=> r1_tarski(k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f55,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f31,f51,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f73,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f63,f38,f70])).

fof(f38,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f29])).

% (20559)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f40,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f52,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f47,f43,f49])).

fof(f43,plain,
    ( spl2_2
  <=> r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f45,f32])).

fof(f45,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f43])).

fof(f30,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f16,f28,f29])).

fof(f16,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (20541)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (20536)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (20547)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (20565)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20548)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (20556)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (20539)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (20556)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (20537)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (20548)Refutation not found, incomplete strategy% (20548)------------------------------
% 0.22/0.52  % (20548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20548)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20548)Memory used [KB]: 10618
% 0.22/0.52  % (20548)Time elapsed: 0.118 s
% 0.22/0.52  % (20548)------------------------------
% 0.22/0.52  % (20548)------------------------------
% 0.22/0.52  % (20537)Refutation not found, incomplete strategy% (20537)------------------------------
% 0.22/0.52  % (20537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20537)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20537)Memory used [KB]: 1663
% 0.22/0.52  % (20537)Time elapsed: 0.084 s
% 0.22/0.52  % (20537)------------------------------
% 0.22/0.52  % (20537)------------------------------
% 0.22/0.52  % (20546)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (20540)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (20565)Refutation not found, incomplete strategy% (20565)------------------------------
% 0.22/0.52  % (20565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20565)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20565)Memory used [KB]: 1663
% 0.22/0.52  % (20565)Time elapsed: 0.120 s
% 0.22/0.52  % (20565)------------------------------
% 0.22/0.52  % (20565)------------------------------
% 0.22/0.52  % (20547)Refutation not found, incomplete strategy% (20547)------------------------------
% 0.22/0.52  % (20547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20547)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20547)Memory used [KB]: 6140
% 0.22/0.52  % (20547)Time elapsed: 0.116 s
% 0.22/0.52  % (20547)------------------------------
% 0.22/0.52  % (20547)------------------------------
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f41,f46,f52,f73,f81,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl2_4 | ~spl2_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    $false | (spl2_4 | ~spl2_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | spl2_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl2_4 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl2_5),
% 0.22/0.52    inference(superposition,[],[f60,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl2_5 <=> sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 0.22/0.52    inference(superposition,[],[f31,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f20,f22,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f19,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f21,f22])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl2_5 | ~spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f49,f78])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl2_3 <=> r1_tarski(k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) | ~spl2_3),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f31,f51,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    r1_tarski(k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))),sK1) | ~spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f49])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~spl2_4 | spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f38,f70])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | spl2_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f40,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f26,f29])).
% 0.22/0.53  % (20559)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f22])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f38])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl2_3 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f43,f49])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    spl2_2 <=> r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    r1_tarski(k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))),sK1) | ~spl2_2),
% 0.22/0.53    inference(forward_demodulation,[],[f45,f32])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f43])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f43])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f28,f29])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ~spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f17,f38])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (20556)------------------------------
% 0.22/0.53  % (20556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20556)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (20556)Memory used [KB]: 10746
% 0.22/0.53  % (20556)Time elapsed: 0.119 s
% 0.22/0.53  % (20556)------------------------------
% 0.22/0.53  % (20556)------------------------------
% 0.22/0.53  % (20554)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (20535)Success in time 0.168 s
%------------------------------------------------------------------------------
