%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:32 EST 2020

% Result     : Theorem 0.09s
% Output     : Refutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  73 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f14])).

fof(f14,plain,(
    sK0 != k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f22,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f21,f13])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(k1_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X1)) = X0
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,k1_relat_1(X0)) = X1 ) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_relat_1(X0))
      | k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0)
      | ~ r3_xboole_0(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f16,f17])).

% (17593)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
     => ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 16:42:09 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.09/0.29  % (17589)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.09/0.29  % (17592)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.09/0.29  % (17596)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.09/0.29  % (17589)Refutation found. Thanks to Tanya!
% 0.09/0.29  % SZS status Theorem for theBenchmark
% 0.09/0.29  % SZS output start Proof for theBenchmark
% 0.09/0.29  fof(f23,plain,(
% 0.09/0.29    $false),
% 0.09/0.29    inference(subsumption_resolution,[],[f22,f14])).
% 0.09/0.29  fof(f14,plain,(
% 0.09/0.29    sK0 != k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.09/0.29    inference(cnf_transformation,[],[f8])).
% 0.09/0.29  fof(f8,plain,(
% 0.09/0.29    ? [X0] : (k7_relat_1(X0,k1_relat_1(X0)) != X0 & v1_relat_1(X0))),
% 0.09/0.29    inference(ennf_transformation,[],[f5])).
% 0.09/0.29  fof(f5,negated_conjecture,(
% 0.09/0.29    ~! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.09/0.29    inference(negated_conjecture,[],[f4])).
% 0.09/0.29  fof(f4,conjecture,(
% 0.09/0.29    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.09/0.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.09/0.29  fof(f22,plain,(
% 0.09/0.29    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.09/0.29    inference(resolution,[],[f21,f13])).
% 0.09/0.29  fof(f13,plain,(
% 0.09/0.29    v1_relat_1(sK0)),
% 0.09/0.29    inference(cnf_transformation,[],[f8])).
% 0.09/0.29  fof(f21,plain,(
% 0.09/0.29    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.09/0.29    inference(duplicate_literal_removal,[],[f20])).
% 0.09/0.29  fof(f20,plain,(
% 0.09/0.29    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.09/0.29    inference(resolution,[],[f19,f15])).
% 0.09/0.29  fof(f15,plain,(
% 0.09/0.29    ( ! [X0] : (r3_xboole_0(X0,X0)) )),
% 0.09/0.29    inference(cnf_transformation,[],[f6])).
% 0.09/0.29  fof(f6,plain,(
% 0.09/0.29    ! [X0] : r3_xboole_0(X0,X0)),
% 0.09/0.29    inference(rectify,[],[f2])).
% 0.09/0.29  fof(f2,axiom,(
% 0.09/0.29    ! [X0,X1] : r3_xboole_0(X0,X0)),
% 0.09/0.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).
% 0.09/0.29  fof(f19,plain,(
% 0.09/0.29    ( ! [X0,X1] : (~r3_xboole_0(k1_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X1)) = X0 | ~v1_relat_1(X1) | k7_relat_1(X1,k1_relat_1(X0)) = X1) )),
% 0.09/0.29    inference(resolution,[],[f18,f16])).
% 0.09/0.29  fof(f16,plain,(
% 0.09/0.29    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.09/0.29    inference(cnf_transformation,[],[f10])).
% 0.09/0.29  fof(f10,plain,(
% 0.09/0.29    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.09/0.29    inference(flattening,[],[f9])).
% 0.09/0.29  fof(f9,plain,(
% 0.09/0.29    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.09/0.29    inference(ennf_transformation,[],[f3])).
% 0.09/0.29  fof(f3,axiom,(
% 0.09/0.29    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.09/0.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.09/0.29  fof(f18,plain,(
% 0.09/0.29    ( ! [X0,X1] : (r1_tarski(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = X0 | ~v1_relat_1(X0) | ~r3_xboole_0(X1,k1_relat_1(X0))) )),
% 0.09/0.29    inference(resolution,[],[f16,f17])).
% 0.09/0.29  % (17593)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.09/0.29  fof(f17,plain,(
% 0.09/0.29    ( ! [X0,X1] : (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)) )),
% 0.09/0.29    inference(cnf_transformation,[],[f12])).
% 0.09/0.29  fof(f12,plain,(
% 0.09/0.29    ! [X0,X1] : (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1))),
% 0.09/0.29    inference(flattening,[],[f11])).
% 0.09/0.29  fof(f11,plain,(
% 0.09/0.29    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1))),
% 0.09/0.29    inference(ennf_transformation,[],[f7])).
% 0.09/0.29  fof(f7,plain,(
% 0.09/0.29    ! [X0,X1] : (r3_xboole_0(X0,X1) => (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.09/0.29    inference(unused_predicate_definition_removal,[],[f1])).
% 0.09/0.29  fof(f1,axiom,(
% 0.09/0.29    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.09/0.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.09/0.29  % SZS output end Proof for theBenchmark
% 0.09/0.29  % (17589)------------------------------
% 0.09/0.29  % (17589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.09/0.29  % (17589)Termination reason: Refutation
% 0.09/0.29  
% 0.09/0.29  % (17589)Memory used [KB]: 10490
% 0.09/0.29  % (17589)Time elapsed: 0.003 s
% 0.09/0.29  % (17589)------------------------------
% 0.09/0.29  % (17589)------------------------------
% 0.09/0.29  % (17587)Success in time 0.033 s
%------------------------------------------------------------------------------
