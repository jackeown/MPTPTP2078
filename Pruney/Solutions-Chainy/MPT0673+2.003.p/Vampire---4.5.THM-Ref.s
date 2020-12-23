%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 158 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(resolution,[],[f31,f15])).

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

fof(f31,plain,(
    ! [X0] : v2_funct_1(k8_relat_1(X0,sK1)) ),
    inference(subsumption_resolution,[],[f30,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
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
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f27,f17])).

fof(f17,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(sK1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f26,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(sK1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f24,f13])).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( v2_funct_1(k8_relat_1(X0,sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(sK1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    inference(resolution,[],[f21,f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (20526)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (20526)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(resolution,[],[f31,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ~v2_funct_1(k8_relat_1(sK0,sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1] : (~v2_funct_1(k8_relat_1(X0,X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0,X1] : ((~v2_funct_1(k8_relat_1(X0,X1)) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k8_relat_1(X0,X1))))),
% 0.20/0.42    inference(negated_conjecture,[],[f5])).
% 0.20/0.42  fof(f5,conjecture,(
% 0.20/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => v2_funct_1(k8_relat_1(X0,X1))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_funct_1)).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f30,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f29,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f28,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    v2_funct_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v2_funct_1(sK1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f27,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(sK1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f26,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(sK1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f24,f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    v1_funct_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k8_relat_1(X0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v2_funct_1(sK1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(superposition,[],[f20,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.20/0.42    inference(resolution,[],[f21,f12])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (20526)------------------------------
% 0.20/0.42  % (20526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (20526)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (20526)Memory used [KB]: 10490
% 0.20/0.42  % (20526)Time elapsed: 0.005 s
% 0.20/0.42  % (20526)------------------------------
% 0.20/0.42  % (20526)------------------------------
% 0.20/0.42  % (20525)Success in time 0.067 s
%------------------------------------------------------------------------------
