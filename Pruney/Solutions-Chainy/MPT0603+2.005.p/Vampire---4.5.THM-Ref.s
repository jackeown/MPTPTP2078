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
% DateTime   : Thu Dec  3 12:51:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 105 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f18])).

fof(f18,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f57,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f54,f17])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X2),X3) ) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK2),X0),X2)
      | ~ r1_xboole_0(X2,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f40,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(k1_relat_1(sK2),X0),X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(forward_demodulation,[],[f38,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0) ),
    inference(resolution,[],[f22,f16])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1) ) ),
    inference(resolution,[],[f33,f16])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3)
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (10205)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.41  % (10203)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  % (10205)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f57,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.20/0.41    inference(flattening,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.41    inference(resolution,[],[f54,f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    r1_xboole_0(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X2),X3)) )),
% 0.20/0.41    inference(resolution,[],[f41,f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.41    inference(superposition,[],[f19,f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(sK2),X0),X2) | ~r1_xboole_0(X2,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 0.20/0.41    inference(resolution,[],[f40,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(flattening,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(k1_relat_1(sK2),X0),X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 0.20/0.41    inference(forward_demodulation,[],[f38,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) )),
% 0.20/0.41    inference(resolution,[],[f22,f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    v1_relat_1(sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1)) )),
% 0.20/0.41    inference(resolution,[],[f33,f16])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3) | ~r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3)) )),
% 0.20/0.41    inference(resolution,[],[f23,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (10205)------------------------------
% 0.20/0.41  % (10205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (10205)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (10205)Memory used [KB]: 10618
% 0.20/0.41  % (10205)Time elapsed: 0.030 s
% 0.20/0.41  % (10205)------------------------------
% 0.20/0.41  % (10205)------------------------------
% 0.20/0.41  % (10202)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (10196)Success in time 0.06 s
%------------------------------------------------------------------------------
