%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   13
%              Number of atoms          :   94 ( 161 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(resolution,[],[f33,f15])).

fof(f15,plain,(
    ~ v2_funct_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_funct_1)).

fof(f33,plain,(
    ! [X0] : v2_funct_1(k8_relat_1(X0,sK1)) ),
    inference(subsumption_resolution,[],[f32,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f31,f19])).

fof(f19,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f17,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f29,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f28,f14])).

fof(f14,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f26,f13])).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_funct_1(sK1)
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f22,f23])).

fof(f23,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    inference(resolution,[],[f20,f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (13440)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (13439)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (13436)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (13436)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(resolution,[],[f33,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ~v2_funct_1(k8_relat_1(sK0,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1] : (~v2_funct_1(k8_relat_1(X0,X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1] : ((~v2_funct_1(k8_relat_1(X0,X1)) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k8_relat_1(X0,X1))))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k8_relat_1(X0,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_funct_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1))) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f32,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f31,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f30,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f29,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f28,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    v2_funct_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f26,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    v1_funct_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.43    inference(superposition,[],[f22,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(resolution,[],[f20,f12])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (13436)------------------------------
% 0.21/0.43  % (13436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (13436)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (13436)Memory used [KB]: 10490
% 0.21/0.43  % (13436)Time elapsed: 0.005 s
% 0.21/0.43  % (13436)------------------------------
% 0.21/0.43  % (13436)------------------------------
% 0.21/0.43  % (13432)Success in time 0.077 s
%------------------------------------------------------------------------------
