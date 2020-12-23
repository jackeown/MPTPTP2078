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
% DateTime   : Thu Dec  3 13:07:08 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 112 expanded)
%              Number of equality atoms :   33 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f50])).

fof(f50,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f49,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f47,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f45,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f67,plain,(
    sK1 != k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f23,f66])).

fof(f66,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f65,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f58,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f25,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k6_partfun1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f57,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f25,f25,f25])).

fof(f31,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f57,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,X1) = k1_relat_1(k5_relat_1(X0,k6_partfun1(X1))) ) ),
    inference(forward_demodulation,[],[f55,f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,k6_partfun1(X1))) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1))) ) ),
    inference(resolution,[],[f30,f39])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f65,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f23,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.32/0.55  % (11332)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.56  % (11324)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.57  % (11320)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.62/0.57  % (11324)Refutation found. Thanks to Tanya!
% 1.62/0.57  % SZS status Theorem for theBenchmark
% 1.62/0.58  % (11320)Refutation not found, incomplete strategy% (11320)------------------------------
% 1.62/0.58  % (11320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (11320)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (11320)Memory used [KB]: 10618
% 1.62/0.58  % (11320)Time elapsed: 0.134 s
% 1.62/0.58  % (11320)------------------------------
% 1.62/0.58  % (11320)------------------------------
% 1.62/0.58  % (11340)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f68,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(subsumption_resolution,[],[f67,f50])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    sK1 = k3_xboole_0(sK1,sK0)),
% 1.62/0.58    inference(resolution,[],[f49,f32])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,plain,(
% 1.62/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    r1_tarski(sK1,sK0)),
% 1.62/0.58    inference(resolution,[],[f47,f43])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(subsumption_resolution,[],[f45,f24])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(resolution,[],[f33,f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.62/0.58    inference(negated_conjecture,[],[f12])).
% 1.62/0.58  fof(f12,conjecture,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f20])).
% 1.62/0.58  fof(f20,plain,(
% 1.62/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.62/0.58    inference(flattening,[],[f19])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    sK1 != k3_xboole_0(sK1,sK0)),
% 1.62/0.58    inference(superposition,[],[f23,f66])).
% 1.62/0.58  fof(f66,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 1.62/0.58    inference(forward_demodulation,[],[f65,f59])).
% 1.62/0.58  fof(f59,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 1.62/0.58    inference(forward_demodulation,[],[f58,f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.62/0.58    inference(definition_unfolding,[],[f28,f25])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.62/0.58  fof(f58,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k6_partfun1(k3_xboole_0(X1,X0)))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f57,f42])).
% 1.62/0.58  fof(f42,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k3_xboole_0(X0,X1))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f31,f25,f25,f25])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1)))) )),
% 1.62/0.58    inference(resolution,[],[f56,f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f26,f25])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.62/0.58    inference(pure_predicate_removal,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(X0,X1) = k1_relat_1(k5_relat_1(X0,k6_partfun1(X1)))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f55,f41])).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,k6_partfun1(X1))) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1)))) )),
% 1.62/0.58    inference(resolution,[],[f30,f39])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 1.62/0.58    inference(resolution,[],[f38,f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,plain,(
% 1.62/0.58    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.62/0.58    inference(pure_predicate_removal,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f21])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (11324)------------------------------
% 1.62/0.58  % (11324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (11324)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (11324)Memory used [KB]: 6268
% 1.62/0.58  % (11324)Time elapsed: 0.138 s
% 1.62/0.58  % (11324)------------------------------
% 1.62/0.58  % (11324)------------------------------
% 1.62/0.58  % (11317)Success in time 0.214 s
%------------------------------------------------------------------------------
