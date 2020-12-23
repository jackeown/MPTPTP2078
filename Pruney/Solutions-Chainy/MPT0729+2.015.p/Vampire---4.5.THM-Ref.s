%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  97 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 164 expanded)
%              Number of equality atoms :   22 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(subsumption_resolution,[],[f183,f33])).

fof(f33,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f29,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f183,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f173,f32])).

fof(f32,plain,(
    k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = k2_xboole_0(sK1,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f11,f31,f31])).

fof(f11,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f173,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f101,f81,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X2,X1))
      | r2_hidden(X0,X2)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f15,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f81,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f71,plain,(
    ~ sP5(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f12,f12,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f88,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f88,plain,(
    r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f56,f78,f15])).

fof(f78,plain,(
    ~ r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f70,f36])).

fof(f70,plain,(
    ~ sP5(sK1,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f12,f12,f22])).

fof(f56,plain,(
    sP3(sK1,k2_tarski(sK0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f34])).

fof(f47,plain,(
    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f33,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (31315)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.48  % (31307)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.49  % (31295)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (31302)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.50  % (31294)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (31297)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.51  % (31292)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (31291)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (31303)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (31303)Refutation not found, incomplete strategy% (31303)------------------------------
% 0.19/0.52  % (31303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (31308)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.52  % (31303)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (31303)Memory used [KB]: 1663
% 0.19/0.52  % (31303)Time elapsed: 0.111 s
% 0.19/0.52  % (31303)------------------------------
% 0.19/0.52  % (31303)------------------------------
% 0.19/0.52  % (31290)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (31290)Refutation not found, incomplete strategy% (31290)------------------------------
% 0.19/0.52  % (31290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (31290)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (31290)Memory used [KB]: 1663
% 0.19/0.52  % (31290)Time elapsed: 0.117 s
% 0.19/0.52  % (31290)------------------------------
% 0.19/0.52  % (31290)------------------------------
% 0.19/0.52  % (31311)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (31308)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f184,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(subsumption_resolution,[],[f183,f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))) )),
% 0.19/0.52    inference(definition_unfolding,[],[f29,f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.19/0.52    inference(definition_unfolding,[],[f27,f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.19/0.52  fof(f183,plain,(
% 0.19/0.52    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 0.19/0.52    inference(forward_demodulation,[],[f173,f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = k2_xboole_0(sK1,k2_tarski(sK1,sK1))),
% 0.19/0.52    inference(definition_unfolding,[],[f11,f31,f31])).
% 0.19/0.52  fof(f11,plain,(
% 0.19/0.52    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,plain,(
% 0.19/0.52    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 0.19/0.52    inference(negated_conjecture,[],[f7])).
% 0.19/0.52  fof(f7,conjecture,(
% 0.19/0.52    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).
% 0.19/0.52  fof(f173,plain,(
% 0.19/0.52    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f101,f81,f65])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(X2,X1)) | r2_hidden(X0,X2) | r2_hidden(X0,X1)) )),
% 0.19/0.52    inference(resolution,[],[f15,f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.19/0.52    inference(equality_resolution,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ~r2_hidden(sK0,k2_tarski(sK1,sK1))),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f71,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.19/0.52    inference(cnf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    ~sP5(sK0,sK1,sK1)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f12,f12,f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 0.19/0.52    inference(cnf_transformation,[],[f3])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    sK0 != sK1),
% 0.19/0.52    inference(cnf_transformation,[],[f9])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    ~r2_hidden(sK0,sK1)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f88,f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,plain,(
% 0.19/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.19/0.52  fof(f88,plain,(
% 0.19/0.52    r2_hidden(sK1,sK0)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f56,f78,f15])).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    ~r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f70,f36])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ~sP5(sK1,sK0,sK0)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f12,f12,f22])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    sP3(sK1,k2_tarski(sK0,sK0),sK0)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f47,f34])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 0.19/0.53    inference(superposition,[],[f33,f32])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (31308)------------------------------
% 0.19/0.53  % (31308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (31308)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (31308)Memory used [KB]: 1791
% 0.19/0.53  % (31308)Time elapsed: 0.130 s
% 0.19/0.53  % (31308)------------------------------
% 0.19/0.53  % (31308)------------------------------
% 0.19/0.53  % (31288)Success in time 0.172 s
%------------------------------------------------------------------------------
