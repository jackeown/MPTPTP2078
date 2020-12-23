%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:20 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 429 expanded)
%              Number of leaves         :   18 ( 114 expanded)
%              Depth                    :   21
%              Number of atoms          :  223 (1099 expanded)
%              Number of equality atoms :   94 ( 469 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(subsumption_resolution,[],[f188,f167])).

fof(f167,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f150,f165])).

fof(f165,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f93,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f93,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_relat_1(sK2),X5)
      | sK2 = k5_relat_1(sK2,k6_relat_1(X5)) ) ),
    inference(resolution,[],[f50,f81])).

fof(f81,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

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

fof(f66,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f150,plain,(
    ! [X5] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X5))) = k10_relat_1(sK2,X5) ),
    inference(resolution,[],[f98,f81])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f95,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f188,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f187,f151])).

fof(f151,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(superposition,[],[f87,f136])).

fof(f136,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f86,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK2,X1)
      | sK2 = k7_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f87,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f81,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f187,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f186,f63])).

fof(f186,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f185,f157])).

fof(f157,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f87,f153])).

fof(f153,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f85,f63])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f81,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f185,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f184,f176])).

% (364)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (375)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (384)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (367)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (370)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (379)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (373)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f176,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[],[f150,f174])).

fof(f174,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(resolution,[],[f164,f76])).

fof(f76,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | sK2 = k5_relat_1(sK2,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f93,f89])).

fof(f89,plain,(
    ! [X4] :
      ( r1_tarski(k2_relat_1(sK2),X4)
      | ~ v5_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f184,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f183,f102])).

fof(f102,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK1,sK0,sK2,X0) ),
    inference(resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f183,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f182,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f181,f157])).

fof(f181,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f180,f176])).

fof(f180,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f177,f102])).

fof(f177,plain,
    ( ~ r1_tarski(k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(extensionality_resolution,[],[f56,f130])).

fof(f130,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f129,f103])).

fof(f103,plain,(
    ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f129,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f128,f101])).

fof(f101,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f128,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(forward_demodulation,[],[f127,f100])).

fof(f100,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f127,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(forward_demodulation,[],[f126,f103])).

fof(f126,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(superposition,[],[f41,f102])).

fof(f41,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (368)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (362)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (363)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (365)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (376)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (371)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (372)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (365)Refutation not found, incomplete strategy% (365)------------------------------
% 0.22/0.55  % (365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (365)Memory used [KB]: 6140
% 0.22/0.55  % (365)Time elapsed: 0.097 s
% 0.22/0.55  % (365)------------------------------
% 0.22/0.55  % (365)------------------------------
% 0.22/0.55  % (383)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (371)Refutation not found, incomplete strategy% (371)------------------------------
% 0.22/0.55  % (371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (371)Memory used [KB]: 10618
% 0.22/0.55  % (371)Time elapsed: 0.114 s
% 0.22/0.55  % (371)------------------------------
% 0.22/0.55  % (371)------------------------------
% 1.20/0.55  % (376)Refutation found. Thanks to Tanya!
% 1.20/0.55  % SZS status Theorem for theBenchmark
% 1.20/0.55  % SZS output start Proof for theBenchmark
% 1.20/0.55  fof(f189,plain,(
% 1.20/0.55    $false),
% 1.20/0.55    inference(subsumption_resolution,[],[f188,f167])).
% 1.20/0.55  fof(f167,plain,(
% 1.20/0.55    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.20/0.55    inference(superposition,[],[f150,f165])).
% 1.20/0.55  fof(f165,plain,(
% 1.20/0.55    sK2 = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),
% 1.20/0.55    inference(resolution,[],[f93,f63])).
% 1.20/0.55  fof(f63,plain,(
% 1.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.20/0.55    inference(equality_resolution,[],[f55])).
% 1.20/0.55  fof(f55,plain,(
% 1.20/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.20/0.55    inference(cnf_transformation,[],[f39])).
% 1.20/0.55  fof(f39,plain,(
% 1.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.55    inference(flattening,[],[f38])).
% 1.20/0.55  fof(f38,plain,(
% 1.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.55    inference(nnf_transformation,[],[f1])).
% 1.20/0.55  fof(f1,axiom,(
% 1.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.20/0.55  fof(f93,plain,(
% 1.20/0.55    ( ! [X5] : (~r1_tarski(k2_relat_1(sK2),X5) | sK2 = k5_relat_1(sK2,k6_relat_1(X5))) )),
% 1.20/0.55    inference(resolution,[],[f50,f81])).
% 1.20/0.55  fof(f81,plain,(
% 1.20/0.55    v1_relat_1(sK2)),
% 1.20/0.55    inference(resolution,[],[f66,f40])).
% 1.20/0.55  fof(f40,plain,(
% 1.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.20/0.55    inference(cnf_transformation,[],[f36])).
% 1.20/0.55  fof(f36,plain,(
% 1.20/0.55    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35])).
% 1.20/0.55  fof(f35,plain,(
% 1.20/0.55    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.20/0.55    introduced(choice_axiom,[])).
% 1.20/0.55  fof(f19,plain,(
% 1.20/0.55    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.20/0.55    inference(ennf_transformation,[],[f18])).
% 1.20/0.55  fof(f18,negated_conjecture,(
% 1.20/0.55    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.20/0.55    inference(negated_conjecture,[],[f17])).
% 1.20/0.55  fof(f17,conjecture,(
% 1.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 1.20/0.55  fof(f66,plain,(
% 1.20/0.55    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 1.20/0.55    inference(resolution,[],[f46,f47])).
% 1.20/0.55  fof(f47,plain,(
% 1.20/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.20/0.55    inference(cnf_transformation,[],[f5])).
% 1.20/0.55  fof(f5,axiom,(
% 1.20/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.20/0.55  fof(f46,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.20/0.55    inference(cnf_transformation,[],[f21])).
% 1.20/0.55  fof(f21,plain,(
% 1.20/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.20/0.55    inference(ennf_transformation,[],[f2])).
% 1.20/0.55  fof(f2,axiom,(
% 1.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.20/0.55  fof(f50,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.20/0.55    inference(cnf_transformation,[],[f26])).
% 1.20/0.55  fof(f26,plain,(
% 1.20/0.55    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.20/0.55    inference(flattening,[],[f25])).
% 1.20/0.55  fof(f25,plain,(
% 1.20/0.55    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.55    inference(ennf_transformation,[],[f10])).
% 1.20/0.55  fof(f10,axiom,(
% 1.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 1.20/0.55  fof(f150,plain,(
% 1.20/0.55    ( ! [X5] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X5))) = k10_relat_1(sK2,X5)) )),
% 1.20/0.55    inference(resolution,[],[f98,f81])).
% 1.20/0.55  fof(f98,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)) )),
% 1.20/0.55    inference(forward_demodulation,[],[f95,f43])).
% 1.20/0.55  fof(f43,plain,(
% 1.20/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.20/0.55    inference(cnf_transformation,[],[f9])).
% 1.20/0.55  fof(f9,axiom,(
% 1.20/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.20/0.55  fof(f95,plain,(
% 1.20/0.55    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 1.20/0.55    inference(resolution,[],[f45,f42])).
% 1.20/0.55  fof(f42,plain,(
% 1.20/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.20/0.55    inference(cnf_transformation,[],[f4])).
% 1.20/0.55  fof(f4,axiom,(
% 1.20/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.20/0.55  fof(f45,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.20/0.55    inference(cnf_transformation,[],[f20])).
% 1.20/0.55  fof(f20,plain,(
% 1.20/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.20/0.55    inference(ennf_transformation,[],[f7])).
% 1.20/0.55  fof(f7,axiom,(
% 1.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.20/0.55  fof(f188,plain,(
% 1.20/0.55    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.20/0.55    inference(forward_demodulation,[],[f187,f151])).
% 1.20/0.55  fof(f151,plain,(
% 1.20/0.55    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 1.20/0.55    inference(superposition,[],[f87,f136])).
% 1.20/0.55  fof(f136,plain,(
% 1.20/0.55    sK2 = k7_relat_1(sK2,sK1)),
% 1.20/0.55    inference(resolution,[],[f86,f75])).
% 1.20/0.55  fof(f75,plain,(
% 1.20/0.55    v4_relat_1(sK2,sK1)),
% 1.20/0.55    inference(resolution,[],[f59,f40])).
% 1.20/0.55  fof(f59,plain,(
% 1.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.20/0.55    inference(cnf_transformation,[],[f32])).
% 1.20/0.55  fof(f32,plain,(
% 1.20/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.55    inference(ennf_transformation,[],[f12])).
% 1.20/0.55  fof(f12,axiom,(
% 1.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.20/0.55  fof(f86,plain,(
% 1.20/0.55    ( ! [X1] : (~v4_relat_1(sK2,X1) | sK2 = k7_relat_1(sK2,X1)) )),
% 1.20/0.55    inference(resolution,[],[f81,f53])).
% 1.20/0.55  fof(f53,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.20/0.55    inference(cnf_transformation,[],[f29])).
% 1.20/0.55  fof(f29,plain,(
% 1.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.20/0.55    inference(flattening,[],[f28])).
% 1.20/0.55  fof(f28,plain,(
% 1.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.20/0.55    inference(ennf_transformation,[],[f8])).
% 1.20/0.55  fof(f8,axiom,(
% 1.20/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.20/0.55  fof(f87,plain,(
% 1.20/0.55    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 1.20/0.55    inference(resolution,[],[f81,f48])).
% 1.20/0.55  fof(f48,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.20/0.55    inference(cnf_transformation,[],[f22])).
% 1.20/0.55  fof(f22,plain,(
% 1.20/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.20/0.55    inference(ennf_transformation,[],[f6])).
% 1.20/0.55  fof(f6,axiom,(
% 1.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.20/0.55  fof(f187,plain,(
% 1.20/0.55    k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.55    inference(subsumption_resolution,[],[f186,f63])).
% 1.20/0.55  fof(f186,plain,(
% 1.20/0.55    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.55    inference(forward_demodulation,[],[f185,f157])).
% 1.20/0.55  fof(f157,plain,(
% 1.20/0.55    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.20/0.55    inference(superposition,[],[f87,f153])).
% 1.20/0.55  fof(f153,plain,(
% 1.20/0.55    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 1.20/0.55    inference(resolution,[],[f85,f63])).
% 1.20/0.55  fof(f85,plain,(
% 1.20/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.20/0.55    inference(resolution,[],[f81,f49])).
% 1.20/0.55  fof(f49,plain,(
% 1.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.20/0.55    inference(cnf_transformation,[],[f24])).
% 1.20/0.55  fof(f24,plain,(
% 1.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.20/0.55    inference(flattening,[],[f23])).
% 1.20/0.55  fof(f23,plain,(
% 1.20/0.55    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.55    inference(ennf_transformation,[],[f11])).
% 1.20/0.55  fof(f11,axiom,(
% 1.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.20/0.55  fof(f185,plain,(
% 1.20/0.55    ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.55    inference(forward_demodulation,[],[f184,f176])).
% 1.20/0.55  % (364)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.20/0.55  % (375)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.20/0.55  % (384)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.20/0.55  % (367)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.20/0.55  % (370)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.56  % (379)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.20/0.56  % (373)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.20/0.56  fof(f176,plain,(
% 1.20/0.56    k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 1.20/0.56    inference(superposition,[],[f150,f174])).
% 1.20/0.56  fof(f174,plain,(
% 1.20/0.56    sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 1.20/0.56    inference(resolution,[],[f164,f76])).
% 1.20/0.56  fof(f76,plain,(
% 1.20/0.56    v5_relat_1(sK2,sK0)),
% 1.20/0.56    inference(resolution,[],[f60,f40])).
% 1.20/0.56  fof(f60,plain,(
% 1.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f32])).
% 1.20/0.56  fof(f164,plain,(
% 1.20/0.56    ( ! [X0] : (~v5_relat_1(sK2,X0) | sK2 = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 1.20/0.56    inference(resolution,[],[f93,f89])).
% 1.20/0.56  fof(f89,plain,(
% 1.20/0.56    ( ! [X4] : (r1_tarski(k2_relat_1(sK2),X4) | ~v5_relat_1(sK2,X4)) )),
% 1.20/0.56    inference(resolution,[],[f81,f51])).
% 1.20/0.56  fof(f51,plain,(
% 1.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f37])).
% 1.20/0.56  fof(f37,plain,(
% 1.20/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.20/0.56    inference(nnf_transformation,[],[f27])).
% 1.20/0.56  fof(f27,plain,(
% 1.20/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.56    inference(ennf_transformation,[],[f3])).
% 1.20/0.56  fof(f3,axiom,(
% 1.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.20/0.56  fof(f184,plain,(
% 1.20/0.56    ~r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,k10_relat_1(sK2,sK0))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(forward_demodulation,[],[f183,f102])).
% 1.20/0.56  fof(f102,plain,(
% 1.20/0.56    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK1,sK0,sK2,X0)) )),
% 1.20/0.56    inference(resolution,[],[f61,f40])).
% 1.20/0.56  fof(f61,plain,(
% 1.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f33])).
% 1.20/0.56  fof(f33,plain,(
% 1.20/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.56    inference(ennf_transformation,[],[f15])).
% 1.20/0.56  fof(f15,axiom,(
% 1.20/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.20/0.56  fof(f183,plain,(
% 1.20/0.56    ~r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(subsumption_resolution,[],[f182,f63])).
% 1.20/0.56  fof(f182,plain,(
% 1.20/0.56    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(forward_demodulation,[],[f181,f157])).
% 1.20/0.56  fof(f181,plain,(
% 1.20/0.56    ~r1_tarski(k9_relat_1(sK2,k1_relat_1(sK2)),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(forward_demodulation,[],[f180,f176])).
% 1.20/0.56  fof(f180,plain,(
% 1.20/0.56    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(forward_demodulation,[],[f177,f102])).
% 1.20/0.56  fof(f177,plain,(
% 1.20/0.56    ~r1_tarski(k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(extensionality_resolution,[],[f56,f130])).
% 1.20/0.56  fof(f130,plain,(
% 1.20/0.56    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(forward_demodulation,[],[f129,f103])).
% 1.20/0.56  fof(f103,plain,(
% 1.20/0.56    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 1.20/0.56    inference(resolution,[],[f62,f40])).
% 1.20/0.56  fof(f62,plain,(
% 1.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f34])).
% 1.20/0.56  fof(f34,plain,(
% 1.20/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.56    inference(ennf_transformation,[],[f16])).
% 1.20/0.56  fof(f16,axiom,(
% 1.20/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.20/0.56  fof(f129,plain,(
% 1.20/0.56    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 1.20/0.56    inference(forward_demodulation,[],[f128,f101])).
% 1.20/0.56  fof(f101,plain,(
% 1.20/0.56    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.20/0.56    inference(resolution,[],[f58,f40])).
% 1.20/0.56  fof(f58,plain,(
% 1.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f31])).
% 1.20/0.56  fof(f31,plain,(
% 1.20/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.56    inference(ennf_transformation,[],[f14])).
% 1.20/0.56  fof(f14,axiom,(
% 1.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.20/0.56  fof(f128,plain,(
% 1.20/0.56    k1_relat_1(sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.20/0.56    inference(forward_demodulation,[],[f127,f100])).
% 1.20/0.56  fof(f100,plain,(
% 1.20/0.56    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.20/0.56    inference(resolution,[],[f57,f40])).
% 1.20/0.56  fof(f57,plain,(
% 1.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f30])).
% 1.20/0.56  fof(f30,plain,(
% 1.20/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.56    inference(ennf_transformation,[],[f13])).
% 1.20/0.56  fof(f13,axiom,(
% 1.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.20/0.56  fof(f127,plain,(
% 1.20/0.56    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.20/0.56    inference(forward_demodulation,[],[f126,f103])).
% 1.20/0.56  fof(f126,plain,(
% 1.20/0.56    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.20/0.56    inference(superposition,[],[f41,f102])).
% 1.20/0.56  fof(f41,plain,(
% 1.20/0.56    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 1.20/0.56    inference(cnf_transformation,[],[f36])).
% 1.20/0.56  fof(f56,plain,(
% 1.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.20/0.56    inference(cnf_transformation,[],[f39])).
% 1.20/0.56  % SZS output end Proof for theBenchmark
% 1.20/0.56  % (376)------------------------------
% 1.20/0.56  % (376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.56  % (376)Termination reason: Refutation
% 1.20/0.56  
% 1.20/0.56  % (376)Memory used [KB]: 1663
% 1.20/0.56  % (376)Time elapsed: 0.117 s
% 1.20/0.56  % (376)------------------------------
% 1.20/0.56  % (376)------------------------------
% 1.20/0.56  % (359)Success in time 0.19 s
%------------------------------------------------------------------------------
