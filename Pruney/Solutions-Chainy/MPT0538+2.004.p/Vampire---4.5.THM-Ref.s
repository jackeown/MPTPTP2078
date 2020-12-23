%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   44 (  48 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f27,f36,f37,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f37,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f32,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f15,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

% (11276)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f15,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,o_0_0_xboole_0),o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f30,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f30,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f27,plain,(
    o_0_0_xboole_0 != k8_relat_1(sK0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f14,f16,f16])).

fof(f16,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f14,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:58:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (11283)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (11296)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (11291)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (11275)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (11275)Refutation not found, incomplete strategy% (11275)------------------------------
% 0.21/0.53  % (11275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11275)Memory used [KB]: 10618
% 0.21/0.53  % (11275)Time elapsed: 0.105 s
% 0.21/0.53  % (11275)------------------------------
% 0.21/0.53  % (11275)------------------------------
% 0.21/0.53  % (11284)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (11291)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (11277)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f27,f36,f37,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f15,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  % (11276)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k8_relat_1(X0,o_0_0_xboole_0),o_0_0_xboole_0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f30,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    v1_relat_1(o_0_0_xboole_0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f15,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    o_0_0_xboole_0 != k8_relat_1(sK0,o_0_0_xboole_0)),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f16,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11291)------------------------------
% 0.21/0.53  % (11291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11291)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11291)Memory used [KB]: 6140
% 0.21/0.53  % (11291)Time elapsed: 0.108 s
% 0.21/0.53  % (11291)------------------------------
% 0.21/0.53  % (11291)------------------------------
% 0.21/0.53  % (11277)Refutation not found, incomplete strategy% (11277)------------------------------
% 0.21/0.53  % (11277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11277)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11277)Memory used [KB]: 10618
% 0.21/0.53  % (11277)Time elapsed: 0.087 s
% 0.21/0.53  % (11277)------------------------------
% 0.21/0.53  % (11277)------------------------------
% 0.21/0.53  % (11266)Success in time 0.163 s
%------------------------------------------------------------------------------
