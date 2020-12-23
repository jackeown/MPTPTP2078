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
% DateTime   : Thu Dec  3 12:57:11 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 136 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 293 expanded)
%              Number of equality atoms :   66 ( 132 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(subsumption_resolution,[],[f120,f89])).

fof(f89,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f88,f80])).

fof(f80,plain,(
    sK2 = k8_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f79,f51])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f79,plain,
    ( sK2 = k8_relat_1(sK1,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f76,f60])).

fof(f60,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X0,X1)
      | k8_relat_1(X1,X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(X1,X0) = X0
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f88,plain,(
    ! [X2] : k10_relat_1(sK2,X2) = k1_relat_1(k8_relat_1(X2,sK2)) ),
    inference(forward_demodulation,[],[f86,f62])).

fof(f62,plain,(
    ! [X2] : k8_relat_1(X2,sK2) = k5_relat_1(sK2,k6_relat_1(X2)) ),
    inference(resolution,[],[f38,f51])).

% (14659)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (14645)Refutation not found, incomplete strategy% (14645)------------------------------
% (14645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14645)Termination reason: Refutation not found, incomplete strategy

% (14645)Memory used [KB]: 10618
% (14645)Time elapsed: 0.103 s
% (14645)------------------------------
% (14645)------------------------------
% (14662)Termination reason: Refutation not found, incomplete strategy

% (14662)Memory used [KB]: 10618
% (14662)Time elapsed: 0.107 s
% (14662)------------------------------
% (14662)------------------------------
% (14659)Refutation not found, incomplete strategy% (14659)------------------------------
% (14659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14659)Termination reason: Refutation not found, incomplete strategy

% (14659)Memory used [KB]: 6140
% (14659)Time elapsed: 0.104 s
% (14659)------------------------------
% (14659)------------------------------
% (14660)Refutation not found, incomplete strategy% (14660)------------------------------
% (14660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14660)Termination reason: Refutation not found, incomplete strategy

% (14660)Memory used [KB]: 1663
% (14660)Time elapsed: 0.105 s
% (14660)------------------------------
% (14660)------------------------------
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f86,plain,(
    ! [X2] : k10_relat_1(sK2,X2) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2))) ),
    inference(resolution,[],[f84,f51])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,X1) = k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f82,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f120,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f119,f116])).

fof(f116,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f119,plain,(
    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f69])).

fof(f69,plain,(
    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[],[f64,f68])).

fof(f68,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f67,f51])).

fof(f67,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f64,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f39,f51])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f118,plain,
    ( k9_relat_1(sK2,sK0) != k2_relat_1(sK2)
    | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f95,f117])).

fof(f117,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f50,f33])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f95,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f93,f94])).

fof(f94,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f93,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f32,f92])).

fof(f92,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f32,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n019.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.10/0.41  % (14646)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.10/0.41  % (14644)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.10/0.41  % (14640)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.10/0.41  % (14645)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.10/0.41  % (14642)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.10/0.41  % (14643)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.10/0.41  % (14642)Refutation not found, incomplete strategy% (14642)------------------------------
% 0.10/0.41  % (14642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.41  % (14642)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.41  
% 0.10/0.41  % (14642)Memory used [KB]: 10618
% 0.10/0.41  % (14642)Time elapsed: 0.077 s
% 0.10/0.41  % (14642)------------------------------
% 0.10/0.41  % (14642)------------------------------
% 0.10/0.41  % (14662)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.10/0.42  % (14657)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.10/0.42  % (14660)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.10/0.42  % (14661)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.10/0.42  % (14638)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.10/0.42  % (14656)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.10/0.42  % (14648)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.10/0.42  % (14654)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.10/0.42  % (14658)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.10/0.42  % (14650)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.10/0.42  % (14649)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.10/0.42  % (14646)Refutation not found, incomplete strategy% (14646)------------------------------
% 0.10/0.42  % (14646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (14646)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.42  
% 0.10/0.42  % (14652)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.10/0.42  % (14646)Memory used [KB]: 6140
% 0.10/0.42  % (14646)Time elapsed: 0.104 s
% 0.10/0.42  % (14646)------------------------------
% 0.10/0.42  % (14646)------------------------------
% 0.10/0.42  % (14655)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.10/0.42  % (14653)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.10/0.42  % (14649)Refutation not found, incomplete strategy% (14649)------------------------------
% 0.10/0.42  % (14649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (14649)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.42  
% 0.10/0.42  % (14649)Memory used [KB]: 10618
% 0.10/0.42  % (14649)Time elapsed: 0.106 s
% 0.10/0.42  % (14649)------------------------------
% 0.10/0.42  % (14649)------------------------------
% 0.10/0.42  % (14655)Refutation not found, incomplete strategy% (14655)------------------------------
% 0.10/0.42  % (14655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (14655)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.42  
% 0.10/0.42  % (14655)Memory used [KB]: 1663
% 0.10/0.42  % (14655)Time elapsed: 0.105 s
% 0.10/0.42  % (14655)------------------------------
% 0.10/0.42  % (14655)------------------------------
% 0.10/0.42  % (14639)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.10/0.42  % (14662)Refutation not found, incomplete strategy% (14662)------------------------------
% 0.10/0.42  % (14662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (14651)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.10/0.42  % (14652)Refutation found. Thanks to Tanya!
% 0.10/0.42  % SZS status Theorem for theBenchmark
% 0.10/0.42  % SZS output start Proof for theBenchmark
% 0.10/0.42  fof(f121,plain,(
% 0.10/0.42    $false),
% 0.10/0.42    inference(subsumption_resolution,[],[f120,f89])).
% 0.10/0.42  fof(f89,plain,(
% 0.10/0.42    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.10/0.42    inference(superposition,[],[f88,f80])).
% 0.10/0.42  fof(f80,plain,(
% 0.10/0.42    sK2 = k8_relat_1(sK1,sK2)),
% 0.10/0.42    inference(subsumption_resolution,[],[f79,f51])).
% 0.10/0.42  fof(f51,plain,(
% 0.10/0.42    v1_relat_1(sK2)),
% 0.10/0.42    inference(resolution,[],[f44,f33])).
% 0.10/0.42  fof(f33,plain,(
% 0.10/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.10/0.42    inference(cnf_transformation,[],[f17])).
% 0.10/0.42  fof(f17,plain,(
% 0.10/0.42    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.42    inference(ennf_transformation,[],[f16])).
% 0.10/0.42  fof(f16,negated_conjecture,(
% 0.10/0.42    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.10/0.42    inference(negated_conjecture,[],[f15])).
% 0.10/0.42  fof(f15,conjecture,(
% 0.10/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.10/0.42  fof(f44,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f26])).
% 0.10/0.42  fof(f26,plain,(
% 0.10/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.42    inference(ennf_transformation,[],[f9])).
% 0.10/0.42  fof(f9,axiom,(
% 0.10/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.10/0.42  fof(f79,plain,(
% 0.10/0.42    sK2 = k8_relat_1(sK1,sK2) | ~v1_relat_1(sK2)),
% 0.10/0.42    inference(resolution,[],[f76,f60])).
% 0.10/0.42  fof(f60,plain,(
% 0.10/0.42    v5_relat_1(sK2,sK1)),
% 0.10/0.42    inference(resolution,[],[f48,f33])).
% 0.10/0.42  fof(f48,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f29])).
% 0.10/0.42  fof(f29,plain,(
% 0.10/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.42    inference(ennf_transformation,[],[f10])).
% 0.10/0.42  fof(f10,axiom,(
% 0.10/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.10/0.42  fof(f76,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~v5_relat_1(X0,X1) | k8_relat_1(X1,X0) = X0 | ~v1_relat_1(X0)) )),
% 0.10/0.42    inference(duplicate_literal_removal,[],[f72])).
% 0.10/0.42  fof(f72,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k8_relat_1(X1,X0) = X0 | ~v1_relat_1(X0) | ~v5_relat_1(X0,X1)) )),
% 0.10/0.42    inference(resolution,[],[f40,f42])).
% 0.10/0.42  fof(f42,plain,(
% 0.10/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f23])).
% 0.10/0.42  fof(f23,plain,(
% 0.10/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.10/0.42    inference(ennf_transformation,[],[f1])).
% 0.10/0.42  fof(f1,axiom,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.10/0.42  fof(f40,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.10/0.42    inference(cnf_transformation,[],[f22])).
% 0.10/0.42  fof(f22,plain,(
% 0.10/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.10/0.42    inference(flattening,[],[f21])).
% 0.10/0.42  fof(f21,plain,(
% 0.10/0.42    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.10/0.42    inference(ennf_transformation,[],[f4])).
% 0.10/0.42  fof(f4,axiom,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.10/0.42  fof(f88,plain,(
% 0.10/0.42    ( ! [X2] : (k10_relat_1(sK2,X2) = k1_relat_1(k8_relat_1(X2,sK2))) )),
% 0.10/0.42    inference(forward_demodulation,[],[f86,f62])).
% 0.10/0.42  fof(f62,plain,(
% 0.10/0.42    ( ! [X2] : (k8_relat_1(X2,sK2) = k5_relat_1(sK2,k6_relat_1(X2))) )),
% 0.10/0.42    inference(resolution,[],[f38,f51])).
% 0.10/0.43  % (14659)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.10/0.43  % (14645)Refutation not found, incomplete strategy% (14645)------------------------------
% 0.10/0.43  % (14645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.43  % (14645)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.43  
% 0.10/0.43  % (14645)Memory used [KB]: 10618
% 0.10/0.43  % (14645)Time elapsed: 0.103 s
% 0.10/0.43  % (14645)------------------------------
% 0.10/0.43  % (14645)------------------------------
% 0.10/0.43  % (14662)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.43  
% 0.10/0.43  % (14662)Memory used [KB]: 10618
% 0.10/0.43  % (14662)Time elapsed: 0.107 s
% 0.10/0.43  % (14662)------------------------------
% 0.10/0.43  % (14662)------------------------------
% 0.10/0.43  % (14659)Refutation not found, incomplete strategy% (14659)------------------------------
% 0.10/0.43  % (14659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.43  % (14659)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.43  
% 0.10/0.43  % (14659)Memory used [KB]: 6140
% 0.10/0.43  % (14659)Time elapsed: 0.104 s
% 0.10/0.43  % (14659)------------------------------
% 0.10/0.43  % (14659)------------------------------
% 0.10/0.43  % (14660)Refutation not found, incomplete strategy% (14660)------------------------------
% 0.10/0.43  % (14660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.43  % (14660)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.43  
% 0.10/0.43  % (14660)Memory used [KB]: 1663
% 0.10/0.43  % (14660)Time elapsed: 0.105 s
% 0.10/0.43  % (14660)------------------------------
% 0.10/0.43  % (14660)------------------------------
% 0.10/0.43  fof(f38,plain,(
% 0.10/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.10/0.43    inference(cnf_transformation,[],[f19])).
% 0.10/0.43  fof(f19,plain,(
% 0.10/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.10/0.43    inference(ennf_transformation,[],[f3])).
% 0.10/0.43  fof(f3,axiom,(
% 0.10/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.10/0.43  fof(f86,plain,(
% 0.10/0.43    ( ! [X2] : (k10_relat_1(sK2,X2) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X2)))) )),
% 0.10/0.43    inference(resolution,[],[f84,f51])).
% 0.10/0.43  fof(f84,plain,(
% 0.10/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(X0,X1) = k1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 0.10/0.43    inference(forward_demodulation,[],[f82,f35])).
% 0.10/0.43  fof(f35,plain,(
% 0.10/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.10/0.43    inference(cnf_transformation,[],[f8])).
% 0.10/0.43  fof(f8,axiom,(
% 0.10/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.10/0.43  fof(f82,plain,(
% 0.10/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))) )),
% 0.10/0.43    inference(resolution,[],[f37,f34])).
% 0.10/0.43  fof(f34,plain,(
% 0.10/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.10/0.43    inference(cnf_transformation,[],[f2])).
% 0.10/0.43  fof(f2,axiom,(
% 0.10/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.10/0.43  fof(f37,plain,(
% 0.10/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.10/0.43    inference(cnf_transformation,[],[f18])).
% 0.10/0.43  fof(f18,plain,(
% 0.10/0.43    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.10/0.43    inference(ennf_transformation,[],[f6])).
% 0.10/0.43  fof(f6,axiom,(
% 0.10/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.10/0.43  fof(f120,plain,(
% 0.10/0.43    k1_relat_1(sK2) != k10_relat_1(sK2,sK1)),
% 0.10/0.43    inference(superposition,[],[f119,f116])).
% 0.10/0.43  fof(f116,plain,(
% 0.10/0.43    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 0.10/0.43    inference(resolution,[],[f49,f33])).
% 0.10/0.43  fof(f49,plain,(
% 0.10/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.10/0.43    inference(cnf_transformation,[],[f30])).
% 0.10/0.43  fof(f30,plain,(
% 0.10/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.43    inference(ennf_transformation,[],[f14])).
% 0.10/0.43  fof(f14,axiom,(
% 0.10/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.10/0.43  fof(f119,plain,(
% 0.10/0.43    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 0.10/0.43    inference(subsumption_resolution,[],[f118,f69])).
% 0.10/0.43  fof(f69,plain,(
% 0.10/0.43    k9_relat_1(sK2,sK0) = k2_relat_1(sK2)),
% 0.10/0.43    inference(superposition,[],[f64,f68])).
% 0.10/0.43  fof(f68,plain,(
% 0.10/0.43    sK2 = k7_relat_1(sK2,sK0)),
% 0.10/0.43    inference(subsumption_resolution,[],[f67,f51])).
% 0.10/0.43  fof(f67,plain,(
% 0.10/0.43    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0)),
% 0.10/0.43    inference(resolution,[],[f43,f59])).
% 0.10/0.43  fof(f59,plain,(
% 0.10/0.43    v4_relat_1(sK2,sK0)),
% 0.10/0.43    inference(resolution,[],[f47,f33])).
% 0.10/0.43  fof(f47,plain,(
% 0.10/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.10/0.43    inference(cnf_transformation,[],[f29])).
% 0.10/0.43  fof(f43,plain,(
% 0.10/0.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.10/0.43    inference(cnf_transformation,[],[f25])).
% 0.10/0.43  fof(f25,plain,(
% 0.10/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.10/0.43    inference(flattening,[],[f24])).
% 0.10/0.43  fof(f24,plain,(
% 0.10/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.10/0.43    inference(ennf_transformation,[],[f7])).
% 0.10/0.43  fof(f7,axiom,(
% 0.10/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.10/0.43  fof(f64,plain,(
% 0.10/0.43    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 0.10/0.43    inference(resolution,[],[f39,f51])).
% 0.10/0.43  fof(f39,plain,(
% 0.10/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.10/0.43    inference(cnf_transformation,[],[f20])).
% 0.10/0.43  fof(f20,plain,(
% 0.10/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.10/0.43    inference(ennf_transformation,[],[f5])).
% 0.10/0.43  fof(f5,axiom,(
% 0.10/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.10/0.43  fof(f118,plain,(
% 0.10/0.43    k9_relat_1(sK2,sK0) != k2_relat_1(sK2) | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 0.10/0.43    inference(backward_demodulation,[],[f95,f117])).
% 0.10/0.43  fof(f117,plain,(
% 0.10/0.43    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 0.10/0.43    inference(resolution,[],[f50,f33])).
% 0.10/0.43  fof(f50,plain,(
% 0.10/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.10/0.43    inference(cnf_transformation,[],[f31])).
% 0.10/0.43  fof(f31,plain,(
% 0.10/0.43    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.43    inference(ennf_transformation,[],[f13])).
% 0.10/0.43  fof(f13,axiom,(
% 0.10/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.10/0.43  fof(f95,plain,(
% 0.10/0.43    k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) | k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)),
% 0.10/0.43    inference(backward_demodulation,[],[f93,f94])).
% 0.10/0.43  fof(f94,plain,(
% 0.10/0.43    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.10/0.43    inference(resolution,[],[f46,f33])).
% 0.10/0.43  fof(f46,plain,(
% 0.10/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.10/0.43    inference(cnf_transformation,[],[f28])).
% 0.10/0.43  fof(f28,plain,(
% 0.10/0.43    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.43    inference(ennf_transformation,[],[f12])).
% 0.10/0.43  fof(f12,axiom,(
% 0.10/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.10/0.43  fof(f93,plain,(
% 0.10/0.43    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.10/0.43    inference(backward_demodulation,[],[f32,f92])).
% 0.10/0.43  fof(f92,plain,(
% 0.10/0.43    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.10/0.43    inference(resolution,[],[f45,f33])).
% 0.10/0.43  fof(f45,plain,(
% 0.10/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.10/0.43    inference(cnf_transformation,[],[f27])).
% 0.10/0.43  fof(f27,plain,(
% 0.10/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.43    inference(ennf_transformation,[],[f11])).
% 0.10/0.43  fof(f11,axiom,(
% 0.10/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.10/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.10/0.43  fof(f32,plain,(
% 0.10/0.43    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.10/0.43    inference(cnf_transformation,[],[f17])).
% 0.10/0.43  % SZS output end Proof for theBenchmark
% 0.10/0.43  % (14652)------------------------------
% 0.10/0.43  % (14652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.43  % (14652)Termination reason: Refutation
% 0.10/0.43  
% 0.10/0.43  % (14652)Memory used [KB]: 6268
% 0.10/0.43  % (14652)Time elapsed: 0.108 s
% 0.10/0.43  % (14652)------------------------------
% 0.10/0.43  % (14652)------------------------------
% 0.10/0.43  % (14647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.10/0.43  % (14637)Success in time 0.165 s
%------------------------------------------------------------------------------
