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
% DateTime   : Thu Dec  3 12:48:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  88 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 294 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f315,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(k7_relat_1(sK3,X1),sK3) ),
    inference(resolution,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f315,plain,(
    ~ r1_tarski(k7_relat_1(sK3,sK0),sK3) ),
    inference(subsumption_resolution,[],[f312,f49])).

fof(f49,plain,(
    ! [X2] : r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2)) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f48,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK3)
      | r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2)) ) ),
    inference(subsumption_resolution,[],[f46,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK3)
      | r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2)) ) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f22,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f312,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK0))
    | ~ r1_tarski(k7_relat_1(sK3,sK0),sK3) ),
    inference(superposition,[],[f114,f135])).

fof(f135,plain,(
    k7_relat_1(sK3,sK0) = k7_relat_1(k7_relat_1(sK3,sK0),sK1) ),
    inference(resolution,[],[f54,f21])).

fof(f54,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k7_relat_1(X3,sK0) = k7_relat_1(k7_relat_1(X3,sK0),sK1) ) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f114,plain,(
    ! [X2] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
      | ~ r1_tarski(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f113,f93])).

fof(f93,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK3)
      | v1_relat_1(X2) ) ),
    inference(superposition,[],[f61,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(sK3,X0)) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f113,plain,(
    ! [X2] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f110,f21])).

fof(f110,plain,(
    ! [X2] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(X2,sK3) ) ),
    inference(resolution,[],[f55,f27])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k7_relat_1(sK3,sK1))
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f24,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (22036)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.46  % (22035)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.47  % (22028)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.47  % (22035)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f315,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(k7_relat_1(sK3,X1),sK3)) )),
% 0.21/0.47    inference(resolution,[],[f21,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v1_relat_1(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    ~r1_tarski(k7_relat_1(sK3,sK0),sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f312,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f21])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2] : (~v1_relat_1(sK3) | r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f46,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2] : (~v1_relat_1(sK2) | ~v1_relat_1(sK3) | r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2))) )),
% 0.21/0.47    inference(resolution,[],[f22,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r1_tarski(sK2,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f312,plain,(
% 0.21/0.47    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK0)) | ~r1_tarski(k7_relat_1(sK3,sK0),sK3)),
% 0.21/0.47    inference(superposition,[],[f114,f135])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    k7_relat_1(sK3,sK0) = k7_relat_1(k7_relat_1(sK3,sK0),sK1)),
% 0.21/0.47    inference(resolution,[],[f54,f21])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X3] : (~v1_relat_1(X3) | k7_relat_1(X3,sK0) = k7_relat_1(k7_relat_1(X3,sK0),sK1)) )),
% 0.21/0.47    inference(resolution,[],[f23,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X2] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~r1_tarski(X2,sK3)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f113,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X2] : (~r1_tarski(X2,sK3) | v1_relat_1(X2)) )),
% 0.21/0.47    inference(superposition,[],[f61,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK3))) )),
% 0.21/0.47    inference(superposition,[],[f33,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK3,X0))) )),
% 0.21/0.47    inference(resolution,[],[f21,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ( ! [X2] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~v1_relat_1(X2) | ~r1_tarski(X2,sK3)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f21])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X2] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~v1_relat_1(X2) | ~v1_relat_1(sK3) | ~r1_tarski(X2,sK3)) )),
% 0.21/0.47    inference(resolution,[],[f55,f27])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k7_relat_1(sK3,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X0)) )),
% 0.21/0.47    inference(resolution,[],[f24,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22035)------------------------------
% 0.21/0.47  % (22035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22035)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22035)Memory used [KB]: 1918
% 0.21/0.47  % (22035)Time elapsed: 0.061 s
% 0.21/0.47  % (22035)------------------------------
% 0.21/0.47  % (22035)------------------------------
% 0.21/0.47  % (22013)Success in time 0.112 s
%------------------------------------------------------------------------------
