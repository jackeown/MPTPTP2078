%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  83 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 224 expanded)
%              Number of equality atoms :   32 (  67 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(global_subsumption,[],[f60,f63])).

fof(f63,plain,(
    k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    inference(superposition,[],[f50,f61])).

fof(f61,plain,(
    sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f58,f26])).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f58,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f57,f22])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | sK3 = k7_relat_1(sK3,sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f56,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0 ) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f50,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(resolution,[],[f49,f26])).

fof(f49,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(resolution,[],[f48,f22])).

fof(f48,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,sK2),sK1)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f45,f25])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK2),sK1) ) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X3)
      | ~ r1_xboole_0(X2,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X3,X1),X2) ) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f60,plain,(
    k1_xboole_0 != k7_relat_1(sK3,sK1) ),
    inference(superposition,[],[f24,f59])).

fof(f59,plain,(
    ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f24,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (2670)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (2675)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.43  % (2671)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (2670)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(global_subsumption,[],[f60,f63])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.22/0.43    inference(superposition,[],[f50,f61])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.43    inference(resolution,[],[f58,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.43    inference(resolution,[],[f57,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f8])).
% 0.22/0.43  fof(f8,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | sK3 = k7_relat_1(sK3,sK2) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(resolution,[],[f56,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.43    inference(resolution,[],[f33,f22])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = X0) )),
% 0.22/0.43    inference(resolution,[],[f28,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 0.22/0.43    inference(resolution,[],[f49,f26])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 0.22/0.43    inference(resolution,[],[f48,f22])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,sK2),sK1) | ~v1_relat_1(X3)) )),
% 0.22/0.43    inference(resolution,[],[f45,f25])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK2),sK1)) )),
% 0.22/0.43    inference(resolution,[],[f35,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    r1_xboole_0(sK1,sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X2,X3,X1] : (~v1_relat_1(X3) | ~r1_xboole_0(X2,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X3,X1),X2)) )),
% 0.22/0.43    inference(resolution,[],[f29,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    k1_xboole_0 != k7_relat_1(sK3,sK1)),
% 0.22/0.43    inference(superposition,[],[f24,f59])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.43    inference(resolution,[],[f32,f22])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (2670)------------------------------
% 0.22/0.43  % (2670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (2670)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (2670)Memory used [KB]: 6140
% 0.22/0.43  % (2670)Time elapsed: 0.004 s
% 0.22/0.43  % (2670)------------------------------
% 0.22/0.43  % (2670)------------------------------
% 0.22/0.44  % (2665)Success in time 0.068 s
%------------------------------------------------------------------------------
