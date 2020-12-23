%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:55 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 206 expanded)
%              Number of equality atoms :   37 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(subsumption_resolution,[],[f261,f26])).

fof(f26,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f261,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f257,f57])).

fof(f57,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f257,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    inference(superposition,[],[f213,f254])).

fof(f254,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f251,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f251,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) = k1_relat_1(k7_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f213,plain,(
    ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k10_relat_1(sK1,X6)) ),
    inference(superposition,[],[f100,f205])).

fof(f205,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) = k10_relat_1(k7_relat_1(sK1,X1),X2) ),
    inference(forward_demodulation,[],[f203,f46])).

fof(f46,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f203,plain,(
    ! [X2,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) ),
    inference(resolution,[],[f199,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(backward_demodulation,[],[f45,f97])).

fof(f97,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f95,f47])).

fof(f47,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f35,f27])).

fof(f95,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f75,f27])).

fof(f75,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f73,f29])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) ) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (25870)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (25864)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  % (25880)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.38/0.54  % (25871)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.38/0.54  % (25882)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.38/0.55  % (25882)Refutation not found, incomplete strategy% (25882)------------------------------
% 1.38/0.55  % (25882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (25882)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (25882)Memory used [KB]: 10618
% 1.38/0.55  % (25882)Time elapsed: 0.121 s
% 1.38/0.55  % (25882)------------------------------
% 1.38/0.55  % (25882)------------------------------
% 1.38/0.55  % (25871)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f262,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(subsumption_resolution,[],[f261,f26])).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.38/0.55    inference(cnf_transformation,[],[f14])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.38/0.56    inference(flattening,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,negated_conjecture,(
% 1.38/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.38/0.56    inference(negated_conjecture,[],[f11])).
% 1.38/0.56  fof(f11,conjecture,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.38/0.56  fof(f261,plain,(
% 1.38/0.56    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.38/0.56    inference(superposition,[],[f257,f57])).
% 1.38/0.56  fof(f57,plain,(
% 1.38/0.56    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.38/0.56    inference(subsumption_resolution,[],[f52,f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    v1_relat_1(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f14])).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    ~v1_relat_1(sK1) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.38/0.56    inference(resolution,[],[f37,f25])).
% 1.38/0.56  fof(f25,plain,(
% 1.38/0.56    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.38/0.56    inference(cnf_transformation,[],[f14])).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f22])).
% 1.38/0.56  fof(f22,plain,(
% 1.38/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(flattening,[],[f21])).
% 1.38/0.56  fof(f21,plain,(
% 1.38/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.38/0.56  fof(f257,plain,(
% 1.38/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) )),
% 1.38/0.56    inference(superposition,[],[f213,f254])).
% 1.38/0.56  fof(f254,plain,(
% 1.38/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) )),
% 1.38/0.56    inference(forward_demodulation,[],[f251,f49])).
% 1.38/0.56  fof(f49,plain,(
% 1.38/0.56    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 1.38/0.56    inference(resolution,[],[f36,f24])).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f20])).
% 1.38/0.56  fof(f20,plain,(
% 1.38/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.38/0.56  fof(f251,plain,(
% 1.38/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.38/0.56    inference(resolution,[],[f41,f24])).
% 1.38/0.56  fof(f41,plain,(
% 1.38/0.56    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) = k1_relat_1(k7_relat_1(X1,X2))) )),
% 1.38/0.56    inference(resolution,[],[f31,f33])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,plain,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.38/0.56  fof(f31,plain,(
% 1.38/0.56    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f15])).
% 1.38/0.56  fof(f15,plain,(
% 1.38/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.38/0.56  fof(f213,plain,(
% 1.38/0.56    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k10_relat_1(sK1,X6))) )),
% 1.38/0.56    inference(superposition,[],[f100,f205])).
% 1.38/0.56  fof(f205,plain,(
% 1.38/0.56    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) = k10_relat_1(k7_relat_1(sK1,X1),X2)) )),
% 1.38/0.56    inference(forward_demodulation,[],[f203,f46])).
% 1.38/0.56  fof(f46,plain,(
% 1.38/0.56    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 1.38/0.56    inference(resolution,[],[f35,f24])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f19])).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f9])).
% 1.38/0.56  fof(f9,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.38/0.56  fof(f203,plain,(
% 1.38/0.56    ( ! [X2,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2))) )),
% 1.38/0.56    inference(resolution,[],[f199,f27])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f10])).
% 1.38/0.56  fof(f10,axiom,(
% 1.38/0.56    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.38/0.56  fof(f199,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1))) )),
% 1.38/0.56    inference(resolution,[],[f38,f24])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f23])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 1.38/0.56  fof(f100,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X1),X0),X0)) )),
% 1.38/0.56    inference(backward_demodulation,[],[f45,f97])).
% 1.38/0.56  fof(f97,plain,(
% 1.38/0.56    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.38/0.56    inference(forward_demodulation,[],[f95,f47])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.38/0.56    inference(resolution,[],[f35,f27])).
% 1.38/0.56  fof(f95,plain,(
% 1.38/0.56    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 1.38/0.56    inference(resolution,[],[f75,f27])).
% 1.38/0.56  fof(f75,plain,(
% 1.38/0.56    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) )),
% 1.38/0.56    inference(forward_demodulation,[],[f73,f29])).
% 1.38/0.56  fof(f29,plain,(
% 1.38/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.38/0.56    inference(cnf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.38/0.56  fof(f73,plain,(
% 1.38/0.56    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))) )),
% 1.38/0.56    inference(resolution,[],[f32,f27])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f16])).
% 1.38/0.56  fof(f16,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.38/0.56  fof(f45,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 1.38/0.56    inference(subsumption_resolution,[],[f44,f27])).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.56    inference(superposition,[],[f34,f29])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.38/0.56    inference(ennf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 1.38/0.56  % SZS output end Proof for theBenchmark
% 1.38/0.56  % (25871)------------------------------
% 1.38/0.56  % (25871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (25871)Termination reason: Refutation
% 1.38/0.56  
% 1.38/0.56  % (25871)Memory used [KB]: 6396
% 1.38/0.56  % (25871)Time elapsed: 0.125 s
% 1.38/0.56  % (25871)------------------------------
% 1.38/0.56  % (25871)------------------------------
% 1.58/0.56  % (25862)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.58/0.56  % (25858)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.58/0.56  % (25854)Success in time 0.195 s
%------------------------------------------------------------------------------
