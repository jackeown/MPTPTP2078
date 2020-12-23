%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  80 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f17])).

fof(f17,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f39,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f38,f21])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f38,plain,(
    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,(
    k6_relat_1(sK1) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f27,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f35,f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f34,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f31,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f33,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f24,f18])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:28:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.38  % (4749)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.19/0.38  % (4749)Refutation found. Thanks to Tanya!
% 0.19/0.38  % SZS status Theorem for theBenchmark
% 0.19/0.38  % SZS output start Proof for theBenchmark
% 0.19/0.38  fof(f40,plain,(
% 0.19/0.38    $false),
% 0.19/0.38    inference(subsumption_resolution,[],[f39,f17])).
% 0.19/0.38  fof(f17,plain,(
% 0.19/0.38    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.19/0.38    inference(cnf_transformation,[],[f10])).
% 0.19/0.38  fof(f10,plain,(
% 0.19/0.38    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.38    inference(ennf_transformation,[],[f9])).
% 0.19/0.38  fof(f9,negated_conjecture,(
% 0.19/0.38    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.19/0.38    inference(negated_conjecture,[],[f8])).
% 0.19/0.38  fof(f8,conjecture,(
% 0.19/0.38    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.19/0.38  fof(f39,plain,(
% 0.19/0.38    sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.19/0.38    inference(forward_demodulation,[],[f38,f21])).
% 0.19/0.38  fof(f21,plain,(
% 0.19/0.38    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.38    inference(cnf_transformation,[],[f5])).
% 0.19/0.38  fof(f5,axiom,(
% 0.19/0.38    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.38  fof(f38,plain,(
% 0.19/0.38    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))),
% 0.19/0.38    inference(superposition,[],[f34,f37])).
% 0.19/0.38  fof(f37,plain,(
% 0.19/0.38    k6_relat_1(sK1) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.19/0.38    inference(resolution,[],[f36,f28])).
% 0.19/0.38  fof(f28,plain,(
% 0.19/0.38    r1_tarski(sK1,sK0)),
% 0.19/0.38    inference(resolution,[],[f27,f16])).
% 0.19/0.38  fof(f16,plain,(
% 0.19/0.38    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.38    inference(cnf_transformation,[],[f10])).
% 0.19/0.38  fof(f27,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.38    inference(cnf_transformation,[],[f1])).
% 0.19/0.38  fof(f1,axiom,(
% 0.19/0.38    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.38  fof(f36,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.19/0.38    inference(forward_demodulation,[],[f35,f21])).
% 0.19/0.38  fof(f35,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.19/0.38    inference(resolution,[],[f25,f18])).
% 0.19/0.38  fof(f18,plain,(
% 0.19/0.38    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.38    inference(cnf_transformation,[],[f7])).
% 0.19/0.38  fof(f7,axiom,(
% 0.19/0.38    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.38  fof(f25,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.19/0.38    inference(cnf_transformation,[],[f15])).
% 0.19/0.38  fof(f15,plain,(
% 0.19/0.38    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.38    inference(flattening,[],[f14])).
% 0.19/0.38  fof(f14,plain,(
% 0.19/0.38    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.38    inference(ennf_transformation,[],[f3])).
% 0.19/0.38  fof(f3,axiom,(
% 0.19/0.38    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.19/0.38  fof(f34,plain,(
% 0.19/0.38    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.19/0.38    inference(forward_demodulation,[],[f33,f32])).
% 0.19/0.38  fof(f32,plain,(
% 0.19/0.38    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.38    inference(forward_demodulation,[],[f31,f30])).
% 0.19/0.38  fof(f30,plain,(
% 0.19/0.38    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.19/0.38    inference(resolution,[],[f22,f18])).
% 0.19/0.38  fof(f22,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.19/0.38    inference(cnf_transformation,[],[f11])).
% 0.19/0.38  fof(f11,plain,(
% 0.19/0.38    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.19/0.38    inference(ennf_transformation,[],[f2])).
% 0.19/0.38  fof(f2,axiom,(
% 0.19/0.38    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.19/0.38  fof(f31,plain,(
% 0.19/0.38    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.38    inference(resolution,[],[f23,f18])).
% 0.19/0.38  fof(f23,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.38    inference(cnf_transformation,[],[f12])).
% 0.19/0.38  fof(f12,plain,(
% 0.19/0.38    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.38    inference(ennf_transformation,[],[f6])).
% 0.19/0.38  fof(f6,axiom,(
% 0.19/0.38    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.19/0.38  fof(f33,plain,(
% 0.19/0.38    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.19/0.38    inference(resolution,[],[f24,f18])).
% 0.19/0.38  fof(f24,plain,(
% 0.19/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.19/0.38    inference(cnf_transformation,[],[f13])).
% 0.19/0.38  fof(f13,plain,(
% 0.19/0.38    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.38    inference(ennf_transformation,[],[f4])).
% 0.19/0.38  fof(f4,axiom,(
% 0.19/0.38    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.38  % SZS output end Proof for theBenchmark
% 0.19/0.38  % (4749)------------------------------
% 0.19/0.38  % (4749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.38  % (4749)Termination reason: Refutation
% 0.19/0.38  
% 0.19/0.38  % (4749)Memory used [KB]: 10490
% 0.19/0.38  % (4749)Time elapsed: 0.004 s
% 0.19/0.38  % (4749)------------------------------
% 0.19/0.38  % (4749)------------------------------
% 0.19/0.38  % (4745)Success in time 0.035 s
%------------------------------------------------------------------------------
