%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:18 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 150 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :   75 ( 327 expanded)
%              Number of equality atoms :   15 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f15,f83])).

fof(f83,plain,(
    ! [X5] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X5) ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f27,f16])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f79,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,X4)) ),
    inference(subsumption_resolution,[],[f77,f63])).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f57])).

fof(f57,plain,(
    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f52,f30])).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f51,f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f50,f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k1_xboole_0),X1)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f49,f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f17,f19])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

% (25539)Refutation not found, incomplete strategy% (25539)------------------------------
% (25539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25539)Termination reason: Refutation not found, incomplete strategy
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

% (25539)Memory used [KB]: 6140
% (25539)Time elapsed: 0.113 s
fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

% (25539)------------------------------
% (25539)------------------------------
fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f77,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(X3,sK3(X3,X4,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,X4)) ) ),
    inference(resolution,[],[f23,f62])).

fof(f62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f57])).

fof(f54,plain,(
    v1_relat_1(k10_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f52,f17])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:03:17 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.49  % (25536)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.49  % (25558)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.50  % (25543)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.50  % (25543)Refutation not found, incomplete strategy% (25543)------------------------------
% 0.18/0.50  % (25543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (25543)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (25543)Memory used [KB]: 10618
% 0.18/0.50  % (25543)Time elapsed: 0.107 s
% 0.18/0.50  % (25543)------------------------------
% 0.18/0.50  % (25543)------------------------------
% 0.18/0.50  % (25545)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.50  % (25545)Refutation not found, incomplete strategy% (25545)------------------------------
% 0.18/0.50  % (25545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (25545)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (25545)Memory used [KB]: 10618
% 0.18/0.50  % (25545)Time elapsed: 0.121 s
% 0.18/0.50  % (25545)------------------------------
% 0.18/0.50  % (25545)------------------------------
% 0.18/0.51  % (25535)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.51  % (25541)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.51  % (25535)Refutation not found, incomplete strategy% (25535)------------------------------
% 0.18/0.51  % (25535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (25535)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (25535)Memory used [KB]: 1663
% 0.18/0.51  % (25535)Time elapsed: 0.126 s
% 0.18/0.51  % (25535)------------------------------
% 0.18/0.51  % (25535)------------------------------
% 0.18/0.51  % (25539)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.51  % (25554)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.51  % (25541)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f97,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(trivial_inequality_removal,[],[f96])).
% 0.18/0.51  fof(f96,plain,(
% 0.18/0.51    k1_xboole_0 != k1_xboole_0),
% 0.18/0.51    inference(superposition,[],[f15,f83])).
% 0.18/0.51  fof(f83,plain,(
% 0.18/0.51    ( ! [X5] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X5)) )),
% 0.18/0.51    inference(resolution,[],[f79,f30])).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    ( ! [X0] : (r2_hidden(sK2(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.18/0.51    inference(resolution,[],[f27,f16])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    v1_xboole_0(k1_xboole_0)),
% 0.18/0.51    inference(cnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    v1_xboole_0(k1_xboole_0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.18/0.51    inference(resolution,[],[f20,f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f12])).
% 0.18/0.51  fof(f12,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.18/0.51    inference(ennf_transformation,[],[f9])).
% 0.18/0.51  fof(f9,plain,(
% 0.18/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.18/0.51    inference(cnf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,plain,(
% 0.18/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.18/0.51    inference(ennf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    ( ! [X4,X3] : (~r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f77,f63])).
% 0.18/0.51  fof(f63,plain,(
% 0.18/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.18/0.51    inference(backward_demodulation,[],[f52,f57])).
% 0.18/0.51  fof(f57,plain,(
% 0.18/0.51    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.18/0.51    inference(resolution,[],[f52,f30])).
% 0.18/0.51  fof(f52,plain,(
% 0.18/0.51    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,k1_xboole_0))) )),
% 0.18/0.51    inference(resolution,[],[f51,f16])).
% 0.18/0.51  fof(f51,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 0.18/0.51    inference(resolution,[],[f50,f19])).
% 0.18/0.51  fof(f50,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k1_xboole_0),X1) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 0.18/0.51    inference(resolution,[],[f49,f16])).
% 0.18/0.51  fof(f49,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.18/0.51    inference(resolution,[],[f24,f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.51    inference(resolution,[],[f17,f19])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,plain,(
% 0.18/0.51    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.18/0.51    inference(unused_predicate_definition_removal,[],[f4])).
% 0.18/0.51  % (25539)Refutation not found, incomplete strategy% (25539)------------------------------
% 0.18/0.51  % (25539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (25539)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  fof(f4,axiom,(
% 0.18/0.51    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.18/0.51  
% 0.18/0.51  % (25539)Memory used [KB]: 6140
% 0.18/0.51  % (25539)Time elapsed: 0.113 s
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f14])).
% 0.18/0.51  % (25539)------------------------------
% 0.18/0.51  % (25539)------------------------------
% 0.18/0.51  fof(f14,plain,(
% 0.18/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.18/0.51    inference(ennf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.18/0.51  fof(f77,plain,(
% 0.18/0.51    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK3(X3,X4,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(X3,k10_relat_1(k1_xboole_0,X4))) )),
% 0.18/0.51    inference(resolution,[],[f23,f62])).
% 0.18/0.51  fof(f62,plain,(
% 0.18/0.51    v1_relat_1(k1_xboole_0)),
% 0.18/0.51    inference(backward_demodulation,[],[f54,f57])).
% 0.18/0.51  fof(f54,plain,(
% 0.18/0.51    v1_relat_1(k10_relat_1(k1_xboole_0,k1_xboole_0))),
% 0.18/0.51    inference(resolution,[],[f52,f17])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f14])).
% 0.18/0.51  fof(f15,plain,(
% 0.18/0.51    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,plain,(
% 0.18/0.51    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.18/0.51    inference(ennf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,negated_conjecture,(
% 0.18/0.51    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.18/0.51    inference(negated_conjecture,[],[f6])).
% 0.18/0.51  fof(f6,conjecture,(
% 0.18/0.51    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (25541)------------------------------
% 0.18/0.51  % (25541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (25541)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (25541)Memory used [KB]: 6268
% 0.18/0.51  % (25541)Time elapsed: 0.129 s
% 0.18/0.51  % (25541)------------------------------
% 0.18/0.51  % (25541)------------------------------
% 0.18/0.51  % (25563)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.51  % (25537)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.51  % (25538)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.51  % (25537)Refutation not found, incomplete strategy% (25537)------------------------------
% 0.18/0.51  % (25537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (25537)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (25537)Memory used [KB]: 10618
% 0.18/0.51  % (25537)Time elapsed: 0.123 s
% 0.18/0.51  % (25537)------------------------------
% 0.18/0.51  % (25537)------------------------------
% 0.18/0.51  % (25556)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.51  % (25558)Refutation not found, incomplete strategy% (25558)------------------------------
% 0.18/0.51  % (25558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (25558)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (25558)Memory used [KB]: 1663
% 0.18/0.51  % (25558)Time elapsed: 0.128 s
% 0.18/0.51  % (25558)------------------------------
% 0.18/0.51  % (25558)------------------------------
% 0.18/0.51  % (25556)Refutation not found, incomplete strategy% (25556)------------------------------
% 0.18/0.51  % (25556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (25556)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (25556)Memory used [KB]: 1663
% 0.18/0.51  % (25556)Time elapsed: 0.091 s
% 0.18/0.51  % (25556)------------------------------
% 0.18/0.51  % (25556)------------------------------
% 0.18/0.51  % (25550)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.51  % (25547)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.51  % (25551)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.51  % (25534)Success in time 0.176 s
%------------------------------------------------------------------------------
