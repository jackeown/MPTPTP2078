%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 503 expanded)
%              Number of leaves         :   17 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  207 (1102 expanded)
%              Number of equality atoms :   81 ( 368 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(subsumption_resolution,[],[f177,f133])).

fof(f133,plain,(
    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f97,f127])).

fof(f127,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f93,f116])).

fof(f116,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f115,f84])).

fof(f84,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(superposition,[],[f73,f76])).

fof(f76,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f75,f72])).

fof(f72,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f66,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f75,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK1) ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f60,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f73,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f115,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k9_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f114,f72])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(sK2,k6_relat_1(k9_relat_1(sK2,sK1))) ),
    inference(superposition,[],[f105,f76])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | k7_relat_1(sK2,X0) = k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k9_relat_1(sK2,X0))) ) ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | k7_relat_1(sK2,X0) = k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) ) ),
    inference(superposition,[],[f53,f73])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f93,plain,(
    ! [X2] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,X2) ),
    inference(forward_demodulation,[],[f91,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

% (18087)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f91,plain,(
    ! [X2] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X2))) ),
    inference(resolution,[],[f74,f54])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f74,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(sK2,X1)) = k10_relat_1(sK2,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f97,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f87,f94])).

fof(f94,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[],[f93,f83])).

fof(f83,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f80,f72])).

fof(f80,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(resolution,[],[f78,f53])).

fof(f78,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f77,f72])).

fof(f77,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f61,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f36,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f79,f84])).

fof(f79,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f71,f62])).

fof(f62,plain,(
    ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f36,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f71,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(backward_demodulation,[],[f70,f65])).

fof(f65,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f69,f64])).

fof(f64,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f36,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f69,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f68,f63])).

fof(f63,plain,(
    ! [X1] : k7_relset_1(sK1,sK0,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f68,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(backward_demodulation,[],[f67,f63])).

fof(f67,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(backward_demodulation,[],[f35,f62])).

fof(f35,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f177,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f73,f172])).

fof(f172,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f171,f72])).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f162,f55])).

fof(f162,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f153,f56])).

fof(f153,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    inference(resolution,[],[f143,f78])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) ) ),
    inference(forward_demodulation,[],[f142,f94])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK0),X0))) ) ),
    inference(subsumption_resolution,[],[f140,f72])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK0),X0))) ) ),
    inference(superposition,[],[f118,f83])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))),X1)
      | ~ v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))
      | m1_subset_1(k5_relat_1(sK2,k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,X0),X1))) ) ),
    inference(resolution,[],[f95,f59])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),X1)
      | ~ v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))
      | ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))),X2)
      | m1_subset_1(k5_relat_1(sK2,k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f41,f93])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:34:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (18080)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (18081)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (18079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (18082)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.56  % (18081)Refutation not found, incomplete strategy% (18081)------------------------------
% 0.22/0.56  % (18081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18081)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18081)Memory used [KB]: 10618
% 0.22/0.56  % (18081)Time elapsed: 0.126 s
% 0.22/0.56  % (18081)------------------------------
% 0.22/0.56  % (18081)------------------------------
% 0.22/0.56  % (18093)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.56  % (18086)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (18077)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.57  % (18080)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (18089)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  % (18094)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.57  % (18078)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.57  % (18096)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.57  % (18088)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (18098)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.57  % (18097)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.57  % (18090)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.57  % (18095)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.57  % (18088)Refutation not found, incomplete strategy% (18088)------------------------------
% 0.22/0.57  % (18088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18088)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (18088)Memory used [KB]: 6268
% 0.22/0.57  % (18088)Time elapsed: 0.143 s
% 0.22/0.57  % (18088)------------------------------
% 0.22/0.57  % (18088)------------------------------
% 0.22/0.57  % (18085)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f180,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f177,f133])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f131])).
% 0.22/0.58  fof(f131,plain,(
% 0.22/0.58    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.58    inference(superposition,[],[f97,f127])).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.58    inference(superposition,[],[f93,f116])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    sK2 = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),
% 0.22/0.58    inference(forward_demodulation,[],[f115,f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.22/0.58    inference(superposition,[],[f73,f76])).
% 0.22/0.58  fof(f76,plain,(
% 0.22/0.58    sK2 = k7_relat_1(sK2,sK1)),
% 0.22/0.58    inference(subsumption_resolution,[],[f75,f72])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    v1_relat_1(sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f66,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 0.22/0.58    inference(resolution,[],[f36,f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.22/0.58    inference(negated_conjecture,[],[f17])).
% 0.22/0.58  fof(f17,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK1)),
% 0.22/0.58    inference(resolution,[],[f60,f55])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    v4_relat_1(sK2,sK1)),
% 0.22/0.58    inference(resolution,[],[f36,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 0.22/0.58    inference(resolution,[],[f72,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    sK2 = k5_relat_1(sK2,k6_relat_1(k9_relat_1(sK2,sK1)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f114,f72])).
% 0.22/0.58  fof(f114,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | sK2 = k5_relat_1(sK2,k6_relat_1(k9_relat_1(sK2,sK1)))),
% 0.22/0.58    inference(superposition,[],[f105,f76])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK2,X0)) | k7_relat_1(sK2,X0) = k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k9_relat_1(sK2,X0)))) )),
% 0.22/0.58    inference(resolution,[],[f85,f59])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | ~v1_relat_1(k7_relat_1(sK2,X0)) | k7_relat_1(sK2,X0) = k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1))) )),
% 0.22/0.58    inference(superposition,[],[f53,f73])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    ( ! [X2] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f91,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f9])).
% 0.22/0.58  % (18087)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X2] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X2)))) )),
% 0.22/0.58    inference(resolution,[],[f74,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK2,X1)) = k10_relat_1(sK2,k1_relat_1(X1))) )),
% 0.22/0.58    inference(resolution,[],[f72,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.58    inference(backward_demodulation,[],[f87,f94])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.22/0.58    inference(superposition,[],[f93,f83])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.22/0.58    inference(subsumption_resolution,[],[f80,f72])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.22/0.58    inference(resolution,[],[f78,f53])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f77,f72])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 0.22/0.58    inference(resolution,[],[f61,f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    v5_relat_1(sK2,sK0)),
% 0.22/0.59    inference(resolution,[],[f36,f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.59    inference(backward_demodulation,[],[f79,f84])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.22/0.59    inference(superposition,[],[f71,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.22/0.59    inference(resolution,[],[f36,f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.22/0.59    inference(backward_demodulation,[],[f70,f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.22/0.59    inference(resolution,[],[f36,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f69,f64])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.22/0.59    inference(resolution,[],[f36,f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.22/0.59    inference(forward_demodulation,[],[f68,f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X1] : (k7_relset_1(sK1,sK0,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 0.22/0.59    inference(resolution,[],[f36,f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)),
% 0.22/0.59    inference(backward_demodulation,[],[f67,f63])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)),
% 0.22/0.59    inference(backward_demodulation,[],[f35,f62])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f177,plain,(
% 0.22/0.59    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.59    inference(superposition,[],[f73,f172])).
% 0.22/0.59  fof(f172,plain,(
% 0.22/0.59    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.59    inference(subsumption_resolution,[],[f171,f72])).
% 0.22/0.59  fof(f171,plain,(
% 0.22/0.59    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.59    inference(resolution,[],[f162,f55])).
% 0.22/0.59  fof(f162,plain,(
% 0.22/0.59    v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.59    inference(resolution,[],[f153,f56])).
% 0.22/0.59  fof(f153,plain,(
% 0.22/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.22/0.59    inference(resolution,[],[f143,f78])).
% 0.22/0.59  fof(f143,plain,(
% 0.22/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f142,f94])).
% 0.22/0.59  fof(f142,plain,(
% 0.22/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK0),X0)))) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f140,f72])).
% 0.22/0.59  fof(f140,plain,(
% 0.22/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK0),X0)))) )),
% 0.22/0.59    inference(superposition,[],[f118,f83])).
% 0.22/0.59  fof(f118,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))),X1) | ~v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) | m1_subset_1(k5_relat_1(sK2,k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,X0),X1)))) )),
% 0.22/0.59    inference(resolution,[],[f95,f59])).
% 0.22/0.59  fof(f95,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(sK2,X0),X1) | ~v1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) | ~r1_tarski(k2_relat_1(k5_relat_1(sK2,k6_relat_1(X0))),X2) | m1_subset_1(k5_relat_1(sK2,k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.59    inference(superposition,[],[f41,f93])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.59    inference(flattening,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.59    inference(ennf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (18080)------------------------------
% 0.22/0.59  % (18080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (18080)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (18080)Memory used [KB]: 6268
% 0.22/0.59  % (18080)Time elapsed: 0.134 s
% 0.22/0.59  % (18080)------------------------------
% 0.22/0.59  % (18080)------------------------------
% 0.22/0.59  % (18074)Success in time 0.223 s
%------------------------------------------------------------------------------
