%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:06 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 140 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   18
%              Number of atoms          :  168 ( 384 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f65])).

fof(f65,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f33,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

% (7761)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

fof(f99,plain,(
    ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(backward_demodulation,[],[f85,f96])).

fof(f96,plain,(
    sK3 = k8_relat_1(sK2,sK3) ),
    inference(resolution,[],[f95,f34])).

fof(f34,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | sK3 = k8_relat_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f93,f69])).

fof(f69,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f68,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f93,plain,(
    ! [X0] :
      ( sK3 = k8_relat_1(X0,sK3)
      | ~ r1_tarski(sK1,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f90,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(X0,sK3),sK3)
      | sK3 = k8_relat_1(X0,sK3)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    ! [X1] :
      ( r1_tarski(sK3,k8_relat_1(X1,sK3))
      | ~ r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f87,f69])).

fof(f87,plain,(
    ! [X1] :
      ( r1_tarski(sK3,k8_relat_1(X1,sK3))
      | ~ r1_tarski(sK1,X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f45,f75])).

fof(f75,plain,(
    sK3 = k8_relat_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f73,f69])).

fof(f73,plain,
    ( sK3 = k8_relat_1(sK1,sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f71,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f70,f69])).

fof(f70,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f67,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f67,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(f85,plain,(
    ~ r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3) ),
    inference(backward_demodulation,[],[f35,f66])).

fof(f66,plain,(
    ! [X1] : k6_relset_1(sK0,sK1,X1,sK3) = k8_relat_1(X1,sK3) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f35,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (7747)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (7745)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (7745)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.54  % (7746)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.27/0.54  % (7749)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f105,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(subsumption_resolution,[],[f99,f65])).
% 1.27/0.54  fof(f65,plain,(
% 1.27/0.54    r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.27/0.54    inference(resolution,[],[f33,f53])).
% 1.27/0.54  fof(f53,plain,(
% 1.27/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.27/0.54    inference(duplicate_literal_removal,[],[f52])).
% 1.27/0.54  fof(f52,plain,(
% 1.27/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.54    inference(equality_resolution,[],[f49])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f32])).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(nnf_transformation,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(flattening,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  % (7761)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.27/0.54  fof(f15,plain,(
% 1.27/0.54    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(flattening,[],[f14])).
% 1.27/0.54  fof(f14,plain,(
% 1.27/0.54    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.27/0.54    inference(negated_conjecture,[],[f11])).
% 1.27/0.54  fof(f11,conjecture,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).
% 1.27/0.54  fof(f99,plain,(
% 1.27/0.54    ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.27/0.54    inference(backward_demodulation,[],[f85,f96])).
% 1.27/0.54  fof(f96,plain,(
% 1.27/0.54    sK3 = k8_relat_1(sK2,sK3)),
% 1.27/0.54    inference(resolution,[],[f95,f34])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    r1_tarski(sK1,sK2)),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f95,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(sK1,X0) | sK3 = k8_relat_1(X0,sK3)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f93,f69])).
% 1.27/0.54  fof(f69,plain,(
% 1.27/0.54    v1_relat_1(sK3)),
% 1.27/0.54    inference(subsumption_resolution,[],[f68,f37])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.27/0.54  fof(f68,plain,(
% 1.27/0.54    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.27/0.54    inference(resolution,[],[f33,f36])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.27/0.54  fof(f93,plain,(
% 1.27/0.54    ( ! [X0] : (sK3 = k8_relat_1(X0,sK3) | ~r1_tarski(sK1,X0) | ~v1_relat_1(sK3)) )),
% 1.27/0.54    inference(resolution,[],[f90,f38])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 1.27/0.54  fof(f90,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(k8_relat_1(X0,sK3),sK3) | sK3 = k8_relat_1(X0,sK3) | ~r1_tarski(sK1,X0)) )),
% 1.27/0.54    inference(resolution,[],[f89,f44])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.27/0.54    inference(flattening,[],[f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.27/0.54    inference(nnf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.27/0.54  fof(f89,plain,(
% 1.27/0.54    ( ! [X1] : (r1_tarski(sK3,k8_relat_1(X1,sK3)) | ~r1_tarski(sK1,X1)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f87,f69])).
% 1.27/0.54  fof(f87,plain,(
% 1.27/0.54    ( ! [X1] : (r1_tarski(sK3,k8_relat_1(X1,sK3)) | ~r1_tarski(sK1,X1) | ~v1_relat_1(sK3)) )),
% 1.27/0.54    inference(superposition,[],[f45,f75])).
% 1.27/0.54  fof(f75,plain,(
% 1.27/0.54    sK3 = k8_relat_1(sK1,sK3)),
% 1.27/0.54    inference(subsumption_resolution,[],[f73,f69])).
% 1.27/0.54  fof(f73,plain,(
% 1.27/0.54    sK3 = k8_relat_1(sK1,sK3) | ~v1_relat_1(sK3)),
% 1.27/0.54    inference(resolution,[],[f71,f39])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(flattening,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.27/0.54  fof(f71,plain,(
% 1.27/0.54    r1_tarski(k2_relat_1(sK3),sK1)),
% 1.27/0.54    inference(subsumption_resolution,[],[f70,f69])).
% 1.27/0.54  fof(f70,plain,(
% 1.27/0.54    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 1.27/0.54    inference(resolution,[],[f67,f40])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(nnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.27/0.54  fof(f67,plain,(
% 1.27/0.54    v5_relat_1(sK3,sK1)),
% 1.27/0.54    inference(resolution,[],[f33,f46])).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.27/0.54    inference(pure_predicate_removal,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.27/0.54  fof(f45,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.27/0.54    inference(flattening,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.27/0.54    inference(ennf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).
% 1.27/0.54  fof(f85,plain,(
% 1.27/0.54    ~r2_relset_1(sK0,sK1,k8_relat_1(sK2,sK3),sK3)),
% 1.27/0.54    inference(backward_demodulation,[],[f35,f66])).
% 1.27/0.54  fof(f66,plain,(
% 1.27/0.54    ( ! [X1] : (k6_relset_1(sK0,sK1,X1,sK3) = k8_relat_1(X1,sK3)) )),
% 1.27/0.54    inference(resolution,[],[f33,f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (7745)------------------------------
% 1.27/0.54  % (7745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (7745)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (7745)Memory used [KB]: 10618
% 1.27/0.54  % (7745)Time elapsed: 0.117 s
% 1.27/0.54  % (7745)------------------------------
% 1.27/0.54  % (7745)------------------------------
% 1.27/0.54  % (7743)Success in time 0.179 s
%------------------------------------------------------------------------------
