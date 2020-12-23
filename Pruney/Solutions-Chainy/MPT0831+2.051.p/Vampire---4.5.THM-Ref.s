%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:59 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 136 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  148 ( 357 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f111,f30])).

fof(f30,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f111,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f73,f88])).

fof(f88,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    ! [X3] :
      ( ~ v4_relat_1(sK3,X3)
      | r1_tarski(k1_relat_1(sK3),X3) ) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f52,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f66,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK1,sK0)),X2)
      | v4_relat_1(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f65,plain,(
    ! [X2] :
      ( v4_relat_1(sK3,X2)
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK1,sK0)),X2)
      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X1] :
      ( ~ v4_relat_1(k2_zfmisc_1(sK1,sK0),X1)
      | v4_relat_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X1] :
      ( v4_relat_1(sK3,X1)
      | ~ v4_relat_1(k2_zfmisc_1(sK1,sK0),X1)
      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f68,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f68,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k1_relat_1(sK3),X0),sK2) ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f63,plain,(
    ~ r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f62,f52])).

fof(f62,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ~ v4_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f54,f52])).

fof(f54,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f53,f46])).

fof(f46,plain,(
    r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f53,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f50,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(backward_demodulation,[],[f31,f47])).

fof(f47,plain,(
    ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f31,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n008.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 14:28:15 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.37  % (2101)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.10/0.38  % (2110)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.10/0.38  % (2110)Refutation not found, incomplete strategy% (2110)------------------------------
% 0.10/0.38  % (2110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.38  % (2110)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.38  
% 0.10/0.38  % (2110)Memory used [KB]: 1663
% 0.10/0.38  % (2110)Time elapsed: 0.062 s
% 0.10/0.38  % (2110)------------------------------
% 0.10/0.38  % (2110)------------------------------
% 0.10/0.38  % (2101)Refutation not found, incomplete strategy% (2101)------------------------------
% 0.10/0.38  % (2101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.38  % (2101)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.38  
% 0.10/0.38  % (2101)Memory used [KB]: 10490
% 0.10/0.38  % (2101)Time elapsed: 0.058 s
% 0.10/0.38  % (2101)------------------------------
% 0.10/0.38  % (2101)------------------------------
% 0.10/0.39  % (2098)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.10/0.39  % (2094)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.10/0.39  % (2104)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.10/0.39  % (2104)Refutation found. Thanks to Tanya!
% 0.10/0.39  % SZS status Theorem for theBenchmark
% 0.10/0.39  % SZS output start Proof for theBenchmark
% 0.10/0.39  fof(f114,plain,(
% 0.10/0.39    $false),
% 0.10/0.39    inference(subsumption_resolution,[],[f111,f30])).
% 0.10/0.39  fof(f30,plain,(
% 0.10/0.39    r1_tarski(sK1,sK2)),
% 0.10/0.39    inference(cnf_transformation,[],[f27])).
% 0.10/0.39  fof(f27,plain,(
% 0.10/0.39    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.10/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26])).
% 0.10/0.39  fof(f26,plain,(
% 0.10/0.39    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.10/0.39    introduced(choice_axiom,[])).
% 0.10/0.39  fof(f14,plain,(
% 0.10/0.39    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.10/0.39    inference(flattening,[],[f13])).
% 0.10/0.39  fof(f13,plain,(
% 0.10/0.39    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.10/0.39    inference(ennf_transformation,[],[f12])).
% 0.10/0.39  fof(f12,negated_conjecture,(
% 0.10/0.39    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.10/0.39    inference(negated_conjecture,[],[f11])).
% 0.10/0.39  fof(f11,conjecture,(
% 0.10/0.39    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.10/0.39  fof(f111,plain,(
% 0.10/0.39    ~r1_tarski(sK1,sK2)),
% 0.10/0.39    inference(resolution,[],[f73,f88])).
% 0.10/0.39  fof(f88,plain,(
% 0.10/0.39    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.10/0.39    inference(resolution,[],[f84,f58])).
% 0.10/0.39  fof(f58,plain,(
% 0.10/0.39    ( ! [X3] : (~v4_relat_1(sK3,X3) | r1_tarski(k1_relat_1(sK3),X3)) )),
% 0.10/0.39    inference(resolution,[],[f52,f35])).
% 0.10/0.39  fof(f35,plain,(
% 0.10/0.39    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f28])).
% 0.10/0.39  fof(f28,plain,(
% 0.10/0.39    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.10/0.39    inference(nnf_transformation,[],[f16])).
% 0.10/0.39  fof(f16,plain,(
% 0.10/0.39    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.10/0.39    inference(ennf_transformation,[],[f5])).
% 0.10/0.39  fof(f5,axiom,(
% 0.10/0.39    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.10/0.39  fof(f52,plain,(
% 0.10/0.39    v1_relat_1(sK3)),
% 0.10/0.39    inference(subsumption_resolution,[],[f49,f33])).
% 0.10/0.39  fof(f33,plain,(
% 0.10/0.39    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.10/0.39    inference(cnf_transformation,[],[f6])).
% 0.10/0.39  fof(f6,axiom,(
% 0.10/0.39    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.10/0.39  fof(f49,plain,(
% 0.10/0.39    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.10/0.39    inference(resolution,[],[f29,f32])).
% 0.10/0.39  fof(f32,plain,(
% 0.10/0.39    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f15])).
% 0.10/0.39  fof(f15,plain,(
% 0.10/0.39    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.10/0.39    inference(ennf_transformation,[],[f3])).
% 0.10/0.39  fof(f3,axiom,(
% 0.10/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.10/0.39  fof(f29,plain,(
% 0.10/0.39    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.10/0.39    inference(cnf_transformation,[],[f27])).
% 0.10/0.39  fof(f84,plain,(
% 0.10/0.39    v4_relat_1(sK3,sK1)),
% 0.10/0.39    inference(resolution,[],[f66,f34])).
% 0.10/0.39  fof(f34,plain,(
% 0.10/0.39    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f7])).
% 0.10/0.39  fof(f7,axiom,(
% 0.10/0.39    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 0.10/0.39  fof(f66,plain,(
% 0.10/0.39    ( ! [X2] : (~r1_tarski(k1_relat_1(k2_zfmisc_1(sK1,sK0)),X2) | v4_relat_1(sK3,X2)) )),
% 0.10/0.39    inference(subsumption_resolution,[],[f65,f33])).
% 0.10/0.39  fof(f65,plain,(
% 0.10/0.39    ( ! [X2] : (v4_relat_1(sK3,X2) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(sK1,sK0)),X2) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))) )),
% 0.10/0.39    inference(resolution,[],[f51,f36])).
% 0.10/0.39  fof(f36,plain,(
% 0.10/0.39    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f28])).
% 0.10/0.39  fof(f51,plain,(
% 0.10/0.39    ( ! [X1] : (~v4_relat_1(k2_zfmisc_1(sK1,sK0),X1) | v4_relat_1(sK3,X1)) )),
% 0.10/0.39    inference(subsumption_resolution,[],[f48,f33])).
% 0.10/0.39  fof(f48,plain,(
% 0.10/0.39    ( ! [X1] : (v4_relat_1(sK3,X1) | ~v4_relat_1(k2_zfmisc_1(sK1,sK0),X1) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))) )),
% 0.10/0.39    inference(resolution,[],[f29,f39])).
% 0.10/0.39  fof(f39,plain,(
% 0.10/0.39    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f21])).
% 0.10/0.39  fof(f21,plain,(
% 0.10/0.39    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.10/0.39    inference(flattening,[],[f20])).
% 0.10/0.39  fof(f20,plain,(
% 0.10/0.39    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.10/0.39    inference(ennf_transformation,[],[f4])).
% 0.10/0.39  fof(f4,axiom,(
% 0.10/0.39    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).
% 0.10/0.39  fof(f73,plain,(
% 0.10/0.39    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | ~r1_tarski(X0,sK2)) )),
% 0.10/0.39    inference(superposition,[],[f68,f37])).
% 0.10/0.39  fof(f37,plain,(
% 0.10/0.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f17])).
% 0.10/0.39  fof(f17,plain,(
% 0.10/0.39    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.10/0.39    inference(ennf_transformation,[],[f2])).
% 0.10/0.39  fof(f2,axiom,(
% 0.10/0.39    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.10/0.39  fof(f68,plain,(
% 0.10/0.39    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_relat_1(sK3),X0),sK2)) )),
% 0.10/0.39    inference(resolution,[],[f63,f40])).
% 0.10/0.39  fof(f40,plain,(
% 0.10/0.39    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f22])).
% 0.10/0.39  fof(f22,plain,(
% 0.10/0.39    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.10/0.39    inference(ennf_transformation,[],[f1])).
% 0.10/0.39  fof(f1,axiom,(
% 0.10/0.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.10/0.39  fof(f63,plain,(
% 0.10/0.39    ~r1_tarski(k1_relat_1(sK3),sK2)),
% 0.10/0.39    inference(subsumption_resolution,[],[f62,f52])).
% 0.10/0.39  fof(f62,plain,(
% 0.10/0.39    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.10/0.39    inference(resolution,[],[f55,f36])).
% 0.10/0.39  fof(f55,plain,(
% 0.10/0.39    ~v4_relat_1(sK3,sK2)),
% 0.10/0.39    inference(subsumption_resolution,[],[f54,f52])).
% 0.10/0.39  fof(f54,plain,(
% 0.10/0.39    ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.10/0.39    inference(subsumption_resolution,[],[f53,f46])).
% 0.10/0.39  fof(f46,plain,(
% 0.10/0.39    r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.10/0.39    inference(resolution,[],[f29,f43])).
% 0.10/0.39  fof(f43,plain,(
% 0.10/0.39    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.10/0.39    inference(condensation,[],[f42])).
% 0.10/0.39  fof(f42,plain,(
% 0.10/0.39    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.10/0.39    inference(cnf_transformation,[],[f25])).
% 0.10/0.39  fof(f25,plain,(
% 0.10/0.39    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.39    inference(flattening,[],[f24])).
% 0.10/0.39  fof(f24,plain,(
% 0.10/0.39    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.10/0.39    inference(ennf_transformation,[],[f10])).
% 0.10/0.39  fof(f10,axiom,(
% 0.10/0.39    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.10/0.39  fof(f53,plain,(
% 0.10/0.39    ~r2_relset_1(sK1,sK0,sK3,sK3) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.10/0.39    inference(superposition,[],[f50,f38])).
% 0.10/0.39  fof(f38,plain,(
% 0.10/0.39    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.10/0.39    inference(cnf_transformation,[],[f19])).
% 0.10/0.39  fof(f19,plain,(
% 0.10/0.39    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.10/0.39    inference(flattening,[],[f18])).
% 0.10/0.39  fof(f18,plain,(
% 0.10/0.39    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.10/0.39    inference(ennf_transformation,[],[f8])).
% 0.10/0.39  fof(f8,axiom,(
% 0.10/0.39    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.10/0.39  fof(f50,plain,(
% 0.10/0.39    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.10/0.39    inference(backward_demodulation,[],[f31,f47])).
% 0.10/0.39  fof(f47,plain,(
% 0.10/0.39    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.10/0.39    inference(resolution,[],[f29,f41])).
% 0.10/0.39  fof(f41,plain,(
% 0.10/0.39    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.10/0.39    inference(cnf_transformation,[],[f23])).
% 0.10/0.39  fof(f23,plain,(
% 0.10/0.39    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.10/0.39    inference(ennf_transformation,[],[f9])).
% 0.10/0.39  fof(f9,axiom,(
% 0.10/0.39    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.10/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.10/0.39  fof(f31,plain,(
% 0.10/0.39    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.10/0.39    inference(cnf_transformation,[],[f27])).
% 0.10/0.39  % SZS output end Proof for theBenchmark
% 0.10/0.39  % (2104)------------------------------
% 0.10/0.39  % (2104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.39  % (2104)Termination reason: Refutation
% 0.10/0.39  
% 0.10/0.39  % (2104)Memory used [KB]: 1663
% 0.10/0.39  % (2104)Time elapsed: 0.078 s
% 0.10/0.39  % (2104)------------------------------
% 0.10/0.39  % (2104)------------------------------
% 0.10/0.39  % (2116)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.10/0.39  % (2105)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.10/0.40  % (2096)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.10/0.40  % (2096)Refutation not found, incomplete strategy% (2096)------------------------------
% 0.10/0.40  % (2096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.40  % (2096)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.40  
% 0.10/0.40  % (2096)Memory used [KB]: 10618
% 0.10/0.40  % (2096)Time elapsed: 0.087 s
% 0.10/0.40  % (2096)------------------------------
% 0.10/0.40  % (2096)------------------------------
% 0.10/0.40  % (2106)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.10/0.40  % (2095)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.10/0.40  % (2097)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.10/0.40  % (2114)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.10/0.40  % (2103)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.10/0.40  % (2103)Refutation not found, incomplete strategy% (2103)------------------------------
% 0.10/0.40  % (2103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.40  % (2103)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.40  
% 0.10/0.40  % (2103)Memory used [KB]: 10618
% 0.10/0.40  % (2103)Time elapsed: 0.097 s
% 0.10/0.40  % (2103)------------------------------
% 0.10/0.40  % (2103)------------------------------
% 0.10/0.41  % (2109)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.10/0.41  % (2109)Refutation not found, incomplete strategy% (2109)------------------------------
% 0.10/0.41  % (2109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.41  % (2109)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.41  
% 0.10/0.41  % (2109)Memory used [KB]: 1663
% 0.10/0.41  % (2109)Time elapsed: 0.098 s
% 0.10/0.41  % (2109)------------------------------
% 0.10/0.41  % (2109)------------------------------
% 0.10/0.41  % (2099)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.10/0.41  % (2092)Success in time 0.149 s
%------------------------------------------------------------------------------
