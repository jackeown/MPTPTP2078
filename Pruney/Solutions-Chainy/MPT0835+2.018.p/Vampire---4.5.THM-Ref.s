%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:18 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 212 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 528 expanded)
%              Number of equality atoms :   82 ( 270 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f151,f69])).

fof(f69,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f151,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f149,f62])).

fof(f62,plain,(
    ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f37,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f149,plain,(
    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f148,f70])).

fof(f70,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f148,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f87,f144])).

fof(f144,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[],[f134,f84])).

fof(f84,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f57])).

fof(f83,plain,
    ( sK2 = k5_relat_1(sK2,k6_relat_1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f81,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f81,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f80,f57])).

fof(f80,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f61,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f134,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f132,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f132,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f108,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f71,f50])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f87,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f68,f86])).

% (13638)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f86,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f85,f57])).

fof(f85,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f45,f79])).

fof(f79,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f78,f57])).

fof(f78,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f60,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f37,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f68,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f67,f63])).

fof(f63,plain,(
    ! [X1] : k7_relset_1(sK1,sK0,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f37,f56])).

% (13639)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

% (13625)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f67,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f66,f63])).

fof(f66,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f65,f62])).

fof(f65,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f64,f59])).

fof(f59,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

% (13629)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(backward_demodulation,[],[f38,f58])).

fof(f58,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f38,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (13621)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (13636)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (13622)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (13620)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (13634)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (13619)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (13633)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (13620)Refutation not found, incomplete strategy% (13620)------------------------------
% 0.21/0.51  % (13620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13620)Memory used [KB]: 10618
% 0.21/0.51  % (13620)Time elapsed: 0.086 s
% 0.21/0.51  % (13620)------------------------------
% 0.21/0.51  % (13620)------------------------------
% 0.21/0.51  % (13618)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (13617)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (13628)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (13635)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.19/0.52  % (13637)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.19/0.52  % (13628)Refutation found. Thanks to Tanya!
% 1.19/0.52  % SZS status Theorem for theBenchmark
% 1.19/0.52  % SZS output start Proof for theBenchmark
% 1.19/0.52  fof(f153,plain,(
% 1.19/0.52    $false),
% 1.19/0.52    inference(subsumption_resolution,[],[f151,f69])).
% 1.19/0.52  fof(f69,plain,(
% 1.19/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.19/0.52    inference(resolution,[],[f57,f42])).
% 1.19/0.52  fof(f42,plain,(
% 1.19/0.52    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f19])).
% 1.19/0.52  fof(f19,plain,(
% 1.19/0.52    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f4])).
% 1.19/0.52  fof(f4,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.19/0.52  fof(f57,plain,(
% 1.19/0.52    v1_relat_1(sK2)),
% 1.19/0.52    inference(resolution,[],[f37,f50])).
% 1.19/0.52  fof(f50,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f28])).
% 1.19/0.52  fof(f28,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.52    inference(ennf_transformation,[],[f9])).
% 1.19/0.52  fof(f9,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.19/0.52  fof(f37,plain,(
% 1.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.19/0.52    inference(cnf_transformation,[],[f35])).
% 1.19/0.52  fof(f35,plain,(
% 1.19/0.52    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).
% 1.19/0.52  fof(f34,plain,(
% 1.19/0.52    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f18,plain,(
% 1.19/0.52    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.52    inference(ennf_transformation,[],[f17])).
% 1.19/0.52  fof(f17,negated_conjecture,(
% 1.19/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.19/0.52    inference(negated_conjecture,[],[f16])).
% 1.19/0.52  fof(f16,conjecture,(
% 1.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.19/0.52  fof(f151,plain,(
% 1.19/0.52    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.19/0.52    inference(superposition,[],[f149,f62])).
% 1.19/0.52  fof(f62,plain,(
% 1.19/0.52    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 1.19/0.52    inference(resolution,[],[f37,f55])).
% 1.19/0.52  fof(f55,plain,(
% 1.19/0.52    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f32])).
% 1.19/0.52  fof(f32,plain,(
% 1.19/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.52    inference(ennf_transformation,[],[f14])).
% 1.19/0.52  fof(f14,axiom,(
% 1.19/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.19/0.52  fof(f149,plain,(
% 1.19/0.52    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 1.19/0.52    inference(subsumption_resolution,[],[f148,f70])).
% 1.19/0.52  fof(f70,plain,(
% 1.19/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.19/0.52    inference(resolution,[],[f57,f43])).
% 1.19/0.52  fof(f43,plain,(
% 1.19/0.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f20])).
% 1.19/0.52  fof(f20,plain,(
% 1.19/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f2])).
% 1.19/0.52  fof(f2,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.19/0.52  fof(f148,plain,(
% 1.19/0.52    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 1.19/0.52    inference(backward_demodulation,[],[f87,f144])).
% 1.19/0.52  fof(f144,plain,(
% 1.19/0.52    k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 1.19/0.52    inference(superposition,[],[f134,f84])).
% 1.19/0.52  fof(f84,plain,(
% 1.19/0.52    sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 1.19/0.52    inference(subsumption_resolution,[],[f83,f57])).
% 1.19/0.52  fof(f83,plain,(
% 1.19/0.52    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) | ~v1_relat_1(sK2)),
% 1.19/0.52    inference(resolution,[],[f81,f46])).
% 1.19/0.52  fof(f46,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f24])).
% 1.19/0.52  fof(f24,plain,(
% 1.19/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(flattening,[],[f23])).
% 1.19/0.52  fof(f23,plain,(
% 1.19/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f8])).
% 1.19/0.52  fof(f8,axiom,(
% 1.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.19/0.52  fof(f81,plain,(
% 1.19/0.52    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.19/0.52    inference(subsumption_resolution,[],[f80,f57])).
% 1.19/0.52  fof(f80,plain,(
% 1.19/0.52    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.19/0.52    inference(resolution,[],[f61,f47])).
% 1.19/0.52  fof(f47,plain,(
% 1.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f36])).
% 1.19/0.52  fof(f36,plain,(
% 1.19/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(nnf_transformation,[],[f25])).
% 1.19/0.52  fof(f25,plain,(
% 1.19/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f1])).
% 1.19/0.52  fof(f1,axiom,(
% 1.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.19/0.52  fof(f61,plain,(
% 1.19/0.52    v5_relat_1(sK2,sK0)),
% 1.19/0.52    inference(resolution,[],[f37,f54])).
% 1.19/0.52  fof(f54,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f31])).
% 1.19/0.52  fof(f31,plain,(
% 1.19/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.52    inference(ennf_transformation,[],[f10])).
% 1.19/0.52  fof(f10,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.19/0.52  fof(f134,plain,(
% 1.19/0.52    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) )),
% 1.19/0.52    inference(forward_demodulation,[],[f132,f40])).
% 1.19/0.52  fof(f40,plain,(
% 1.19/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.19/0.52    inference(cnf_transformation,[],[f7])).
% 1.19/0.52  fof(f7,axiom,(
% 1.19/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.19/0.52  fof(f132,plain,(
% 1.19/0.52    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))) )),
% 1.19/0.52    inference(resolution,[],[f108,f39])).
% 1.19/0.52  fof(f39,plain,(
% 1.19/0.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f15])).
% 1.19/0.52  fof(f15,axiom,(
% 1.19/0.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.19/0.52  fof(f108,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))) )),
% 1.19/0.52    inference(resolution,[],[f71,f50])).
% 1.19/0.52  fof(f71,plain,(
% 1.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))) )),
% 1.19/0.52    inference(resolution,[],[f57,f44])).
% 1.19/0.52  fof(f44,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f21])).
% 1.19/0.52  fof(f21,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f5])).
% 1.19/0.52  fof(f5,axiom,(
% 1.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.19/0.52  fof(f87,plain,(
% 1.19/0.52    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 1.19/0.52    inference(backward_demodulation,[],[f68,f86])).
% 1.19/0.52  % (13638)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.19/0.52  fof(f86,plain,(
% 1.19/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 1.19/0.52    inference(subsumption_resolution,[],[f85,f57])).
% 1.19/0.52  fof(f85,plain,(
% 1.19/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.19/0.52    inference(superposition,[],[f45,f79])).
% 1.19/0.52  fof(f79,plain,(
% 1.19/0.52    sK2 = k7_relat_1(sK2,sK1)),
% 1.19/0.52    inference(subsumption_resolution,[],[f78,f57])).
% 1.19/0.52  fof(f78,plain,(
% 1.19/0.52    sK2 = k7_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.19/0.52    inference(resolution,[],[f60,f49])).
% 1.19/0.52  fof(f49,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f27])).
% 1.19/0.52  fof(f27,plain,(
% 1.19/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(flattening,[],[f26])).
% 1.19/0.52  fof(f26,plain,(
% 1.19/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.19/0.52    inference(ennf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,axiom,(
% 1.19/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.19/0.52  fof(f60,plain,(
% 1.19/0.52    v4_relat_1(sK2,sK1)),
% 1.19/0.52    inference(resolution,[],[f37,f53])).
% 1.19/0.52  fof(f53,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f31])).
% 1.19/0.52  fof(f45,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f22])).
% 1.19/0.52  fof(f22,plain,(
% 1.19/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f3])).
% 1.19/0.52  fof(f3,axiom,(
% 1.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.19/0.52  fof(f68,plain,(
% 1.19/0.52    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))),
% 1.19/0.52    inference(forward_demodulation,[],[f67,f63])).
% 1.19/0.52  fof(f63,plain,(
% 1.19/0.52    ( ! [X1] : (k7_relset_1(sK1,sK0,sK2,X1) = k9_relat_1(sK2,X1)) )),
% 1.19/0.52    inference(resolution,[],[f37,f56])).
% 1.19/0.52  % (13639)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.19/0.52  fof(f56,plain,(
% 1.19/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f33])).
% 1.19/0.52  fof(f33,plain,(
% 1.19/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.52    inference(ennf_transformation,[],[f13])).
% 1.19/0.52  fof(f13,axiom,(
% 1.19/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.19/0.52  % (13625)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.19/0.52  fof(f67,plain,(
% 1.19/0.52    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.19/0.52    inference(backward_demodulation,[],[f66,f63])).
% 1.19/0.52  fof(f66,plain,(
% 1.19/0.52    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.19/0.52    inference(backward_demodulation,[],[f65,f62])).
% 1.19/0.52  fof(f65,plain,(
% 1.19/0.52    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 1.19/0.52    inference(backward_demodulation,[],[f64,f59])).
% 1.19/0.52  fof(f59,plain,(
% 1.19/0.52    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.19/0.52    inference(resolution,[],[f37,f52])).
% 1.19/0.52  fof(f52,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f30])).
% 1.19/0.52  fof(f30,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.52    inference(ennf_transformation,[],[f12])).
% 1.19/0.52  % (13629)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.19/0.52  fof(f12,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.19/0.52  fof(f64,plain,(
% 1.19/0.52    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.19/0.52    inference(backward_demodulation,[],[f38,f58])).
% 1.19/0.52  fof(f58,plain,(
% 1.19/0.52    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.19/0.52    inference(resolution,[],[f37,f51])).
% 1.19/0.52  fof(f51,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f29])).
% 1.19/0.52  fof(f29,plain,(
% 1.19/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.52    inference(ennf_transformation,[],[f11])).
% 1.19/0.52  fof(f11,axiom,(
% 1.19/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.19/0.52  fof(f38,plain,(
% 1.19/0.52    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.19/0.52    inference(cnf_transformation,[],[f35])).
% 1.19/0.52  % SZS output end Proof for theBenchmark
% 1.19/0.52  % (13628)------------------------------
% 1.19/0.52  % (13628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (13628)Termination reason: Refutation
% 1.19/0.52  
% 1.19/0.52  % (13628)Memory used [KB]: 1663
% 1.19/0.52  % (13628)Time elapsed: 0.105 s
% 1.19/0.52  % (13628)------------------------------
% 1.19/0.52  % (13628)------------------------------
% 1.19/0.52  % (13626)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.19/0.52  % (13616)Success in time 0.151 s
%------------------------------------------------------------------------------
