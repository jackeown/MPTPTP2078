%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 173 expanded)
%              Number of leaves         :   10 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 256 expanded)
%              Number of equality atoms :   37 ( 139 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f63])).

fof(f63,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f17,f37,f21,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f113,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f94,f106])).

fof(f106,plain,(
    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f46])).

% (15394)Refutation not found, incomplete strategy% (15394)------------------------------
% (15394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15394)Termination reason: Refutation not found, incomplete strategy

% (15394)Memory used [KB]: 1663
% (15394)Time elapsed: 0.149 s
% (15394)------------------------------
% (15394)------------------------------
% (15381)Refutation not found, incomplete strategy% (15381)------------------------------
% (15381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15381)Termination reason: Refutation not found, incomplete strategy

% (15381)Memory used [KB]: 10618
% (15381)Time elapsed: 0.153 s
% (15381)------------------------------
% (15381)------------------------------
fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f105,plain,(
    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f97,f78])).

fof(f78,plain,(
    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f57,plain,(
    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f54,f40])).

fof(f54,plain,(
    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f39,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f16,f37])).

fof(f16,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f79,plain,(
    ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f94,plain,(
    k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) ),
    inference(resolution,[],[f78,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ) ),
    inference(definition_unfolding,[],[f24,f37,f21,f37])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15388)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (15380)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (15372)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (15371)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15373)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (15369)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (15387)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (15389)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (15390)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (15379)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (15365)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (15381)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (15378)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (15366)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (15393)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (15392)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (15366)Refutation not found, incomplete strategy% (15366)------------------------------
% 0.21/0.54  % (15366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15366)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15366)Memory used [KB]: 1663
% 0.21/0.54  % (15366)Time elapsed: 0.125 s
% 0.21/0.54  % (15366)------------------------------
% 0.21/0.54  % (15366)------------------------------
% 0.21/0.54  % (15367)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (15370)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (15368)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (15394)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (15382)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (15374)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (15382)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (15386)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (15376)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (15385)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (15384)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (15377)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (15379)Refutation not found, incomplete strategy% (15379)------------------------------
% 0.21/0.55  % (15379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15379)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15379)Memory used [KB]: 1791
% 0.21/0.56  % (15379)Time elapsed: 0.142 s
% 0.21/0.56  % (15379)------------------------------
% 0.21/0.56  % (15379)------------------------------
% 0.21/0.56  % (15392)Refutation not found, incomplete strategy% (15392)------------------------------
% 0.21/0.56  % (15392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15392)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15392)Memory used [KB]: 6140
% 0.21/0.56  % (15392)Time elapsed: 0.149 s
% 0.21/0.56  % (15392)------------------------------
% 0.21/0.56  % (15392)------------------------------
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.56    inference(superposition,[],[f38,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.21/0.56    inference(definition_unfolding,[],[f17,f37,f21,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f18,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f20,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.56    inference(backward_demodulation,[],[f94,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.56    inference(resolution,[],[f105,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f46])).
% 0.21/0.56  % (15394)Refutation not found, incomplete strategy% (15394)------------------------------
% 0.21/0.56  % (15394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15394)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15394)Memory used [KB]: 1663
% 0.21/0.56  % (15394)Time elapsed: 0.149 s
% 0.21/0.56  % (15394)------------------------------
% 0.21/0.56  % (15394)------------------------------
% 0.21/0.56  % (15381)Refutation not found, incomplete strategy% (15381)------------------------------
% 0.21/0.56  % (15381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15381)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15381)Memory used [KB]: 10618
% 0.21/0.56  % (15381)Time elapsed: 0.153 s
% 0.21/0.56  % (15381)------------------------------
% 0.21/0.56  % (15381)------------------------------
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.56    inference(definition_unfolding,[],[f26,f37])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f97,f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)),
% 0.21/0.56    inference(resolution,[],[f57,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.56    inference(forward_demodulation,[],[f54,f40])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.56    inference(resolution,[],[f39,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.56    inference(definition_unfolding,[],[f16,f37])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.56    inference(resolution,[],[f79,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.56    inference(resolution,[],[f57,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))),
% 0.21/0.56    inference(resolution,[],[f78,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f24,f37,f21,f37])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (15382)------------------------------
% 0.21/0.57  % (15382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15382)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (15382)Memory used [KB]: 1791
% 0.21/0.57  % (15382)Time elapsed: 0.134 s
% 0.21/0.57  % (15382)------------------------------
% 0.21/0.57  % (15382)------------------------------
% 0.21/0.57  % (15364)Success in time 0.199 s
%------------------------------------------------------------------------------
