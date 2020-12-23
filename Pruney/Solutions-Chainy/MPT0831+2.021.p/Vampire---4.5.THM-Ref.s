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
% DateTime   : Thu Dec  3 12:56:54 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 106 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  144 ( 288 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f30])).

fof(f30,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

% (6579)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f129,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f128,f71])).

fof(f71,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f128,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f48,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f47,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ v4_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f122,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f120,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f39,f49])).

fof(f49,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f38,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f120,plain,(
    ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f119,f48])).

fof(f119,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f118,f104])).

fof(f104,plain,(
    r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(resolution,[],[f46,f29])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f118,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f117,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f117,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(subsumption_resolution,[],[f116,f29])).

fof(f116,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f31,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:21:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (6560)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (6561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (6583)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (6562)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (6564)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.50/0.56  % (6564)Refutation not found, incomplete strategy% (6564)------------------------------
% 1.50/0.56  % (6564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (6564)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (6564)Memory used [KB]: 10618
% 1.50/0.56  % (6564)Time elapsed: 0.126 s
% 1.50/0.56  % (6564)------------------------------
% 1.50/0.56  % (6564)------------------------------
% 1.50/0.56  % (6562)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f130,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(subsumption_resolution,[],[f129,f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    r1_tarski(sK1,sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  % (6579)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.50/0.56  fof(f14,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.50/0.56    inference(flattening,[],[f13])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.50/0.56    inference(ennf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 1.50/0.56    inference(negated_conjecture,[],[f11])).
% 1.50/0.56  fof(f11,conjecture,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).
% 1.50/0.56  fof(f129,plain,(
% 1.50/0.56    ~r1_tarski(sK1,sK2)),
% 1.50/0.56    inference(resolution,[],[f128,f71])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    v4_relat_1(sK3,sK1)),
% 1.50/0.56    inference(resolution,[],[f40,f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.50/0.56  fof(f128,plain,(
% 1.50/0.56    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~r1_tarski(X0,sK2)) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f124,f48])).
% 1.50/0.56  fof(f48,plain,(
% 1.50/0.56    v1_relat_1(sK3)),
% 1.50/0.56    inference(subsumption_resolution,[],[f47,f33])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.50/0.56    inference(resolution,[],[f32,f29])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.50/0.56  fof(f124,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,sK2) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 1.50/0.56    inference(resolution,[],[f122,f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(nnf_transformation,[],[f18])).
% 1.50/0.56  fof(f18,plain,(
% 1.50/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.50/0.56  fof(f122,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | ~r1_tarski(X0,sK2)) )),
% 1.50/0.56    inference(resolution,[],[f120,f59])).
% 1.50/0.56  fof(f59,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r1_tarski(X2,X1) | ~r1_tarski(X1,X0)) )),
% 1.50/0.56    inference(superposition,[],[f39,f49])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 1.50/0.56    inference(superposition,[],[f38,f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.50/0.56  fof(f120,plain,(
% 1.50/0.56    ~r1_tarski(k1_relat_1(sK3),sK2)),
% 1.50/0.56    inference(subsumption_resolution,[],[f119,f48])).
% 1.50/0.56  fof(f119,plain,(
% 1.50/0.56    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 1.50/0.56    inference(subsumption_resolution,[],[f118,f104])).
% 1.50/0.56  fof(f104,plain,(
% 1.50/0.56    r2_relset_1(sK1,sK0,sK3,sK3)),
% 1.50/0.56    inference(resolution,[],[f46,f29])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f45])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.56    inference(equality_resolution,[],[f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f28])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(nnf_transformation,[],[f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(flattening,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.50/0.56  fof(f118,plain,(
% 1.50/0.56    ~r2_relset_1(sK1,sK0,sK3,sK3) | ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 1.50/0.56    inference(superposition,[],[f117,f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(flattening,[],[f16])).
% 1.50/0.56  fof(f16,plain,(
% 1.50/0.56    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.50/0.56  fof(f117,plain,(
% 1.50/0.56    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 1.50/0.56    inference(subsumption_resolution,[],[f116,f29])).
% 1.50/0.56  fof(f116,plain,(
% 1.50/0.56    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.56    inference(superposition,[],[f31,f42])).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (6562)------------------------------
% 1.50/0.56  % (6562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (6562)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (6562)Memory used [KB]: 6140
% 1.50/0.56  % (6562)Time elapsed: 0.117 s
% 1.50/0.56  % (6562)------------------------------
% 1.50/0.56  % (6562)------------------------------
% 1.50/0.56  % (6563)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.50/0.56  % (6569)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.50/0.56  % (6571)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.50/0.57  % (6557)Success in time 0.204 s
%------------------------------------------------------------------------------
