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
% DateTime   : Thu Dec  3 12:51:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   24 (  42 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  96 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,(
    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f15,f30])).

fof(f30,plain,(
    ! [X0] : k7_relat_1(sK2,k6_subset_1(sK0,X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0)) ),
    inference(superposition,[],[f20,f25])).

fof(f25,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f24,f19])).

fof(f19,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k1_relat_1(X2),X0)
         => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f24,plain,(
    k7_relat_1(sK2,k1_relat_1(sK2)) = k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f13,f14,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f14,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f13,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f15,plain,(
    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:59:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (24709)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.52  % (24704)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (24725)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.53  % (24705)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (24705)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(trivial_inequality_removal,[],[f39])).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.23/0.53    inference(superposition,[],[f15,f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ( ! [X0] : (k7_relat_1(sK2,k6_subset_1(sK0,X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0))) )),
% 0.23/0.53    inference(superposition,[],[f20,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    sK2 = k7_relat_1(sK2,sK0)),
% 0.23/0.53    inference(forward_demodulation,[],[f24,f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f13,f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    v1_relat_1(sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1)) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2))),
% 0.23/0.53    inference(flattening,[],[f7])).
% 0.23/0.53  fof(f7,plain,(
% 0.23/0.53    ? [X0,X1,X2] : ((k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1)) & r1_tarski(k1_relat_1(X2),X0)) & v1_relat_1(X2))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1))))),
% 0.23/0.53    inference(negated_conjecture,[],[f5])).
% 0.23/0.53  fof(f5,conjecture,(
% 0.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    k7_relat_1(sK2,k1_relat_1(sK2)) = k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK2)),sK0)),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f13,f14,f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.23/0.53    inference(flattening,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k7_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) )),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f13,f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.23/0.53    inference(ennf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1))),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (24705)------------------------------
% 0.23/0.53  % (24705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (24705)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (24705)Memory used [KB]: 6140
% 0.23/0.53  % (24705)Time elapsed: 0.108 s
% 0.23/0.53  % (24705)------------------------------
% 0.23/0.53  % (24705)------------------------------
% 0.23/0.53  % (24700)Success in time 0.157 s
%------------------------------------------------------------------------------
