%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 124 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 190 expanded)
%              Number of equality atoms :   32 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f56,f63,f67])).

fof(f67,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl3_4
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f29,f55,f62,f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f62,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_5
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f55,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_4
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f18,f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f63,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f39,f34,f60])).

fof(f34,plain,
    ( spl3_1
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f36,f43])).

fof(f43,plain,
    ( sK0 = sK2
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f24,f25,f26])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f41,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f36,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f56,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f39,f53])).

fof(f45,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f41,f43])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f39])).

fof(f28,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f15,f25,f26])).

fof(f15,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f34])).

fof(f27,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f16,f25,f26])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.52  % (18478)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (18481)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (18469)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (18498)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (18478)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (18467)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (18490)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (18491)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (18482)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (18497)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (18496)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (18498)Refutation not found, incomplete strategy% (18498)------------------------------
% 0.22/0.54  % (18498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18471)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (18498)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18498)Memory used [KB]: 1663
% 0.22/0.54  % (18498)Time elapsed: 0.118 s
% 0.22/0.54  % (18498)------------------------------
% 0.22/0.54  % (18498)------------------------------
% 0.22/0.54  % (18470)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (18473)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (18472)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (18474)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f37,f42,f56,f63,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ~spl3_4 | spl3_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    $false | (~spl3_4 | spl3_5)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f29,f55,f62,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    spl3_5 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    spl3_4 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f18,f26,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f19,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f17,f25])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ~spl3_5 | spl3_1 | ~spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f39,f34,f60])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    spl3_1 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    spl3_2 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(backward_demodulation,[],[f36,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    sK0 = sK2 | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f41,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) | X0 = X2) )),
% 0.22/0.54    inference(definition_unfolding,[],[f24,f25,f26])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f39])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2) | spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f34])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    spl3_4 | ~spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f39,f53])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_2),
% 0.22/0.54    inference(backward_demodulation,[],[f41,f43])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f28,f39])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.22/0.54    inference(definition_unfolding,[],[f15,f25,f26])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ~spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f27,f34])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.22/0.54    inference(definition_unfolding,[],[f16,f25,f26])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (18478)------------------------------
% 0.22/0.54  % (18478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18478)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (18478)Memory used [KB]: 10746
% 0.22/0.54  % (18478)Time elapsed: 0.113 s
% 0.22/0.54  % (18478)------------------------------
% 0.22/0.54  % (18478)------------------------------
% 0.22/0.54  % (18493)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (18463)Success in time 0.185 s
%------------------------------------------------------------------------------
