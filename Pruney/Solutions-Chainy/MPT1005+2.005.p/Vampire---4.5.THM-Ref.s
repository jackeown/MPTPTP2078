%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 136 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   19
%              Number of atoms          :  101 ( 336 expanded)
%              Number of equality atoms :   43 ( 172 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f52,f97])).

fof(f97,plain,(
    ! [X5] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X5) ),
    inference(resolution,[],[f91,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f91,plain,(
    ! [X1] : v1_xboole_0(k9_relat_1(k1_xboole_0,X1)) ),
    inference(subsumption_resolution,[],[f90,f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_relat_1(k1_xboole_0,X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(superposition,[],[f77,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f77,plain,(
    ! [X6,X5] : v1_xboole_0(k7_relset_1(X5,k1_xboole_0,k1_xboole_0,X6)) ),
    inference(resolution,[],[f69,f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(k7_relset_1(X0,k1_xboole_0,X1,X2)) ) ),
    inference(forward_demodulation,[],[f64,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k7_relset_1(X0,k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f36,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f36,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f22,f34])).

fof(f34,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) ) ),
    inference(resolution,[],[f40,f30])).

fof(f52,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f46,f48])).

fof(f46,plain,(
    k1_xboole_0 != k9_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f45,f35])).

fof(f45,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k9_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f44,f34])).

fof(f44,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(superposition,[],[f23,f24])).

fof(f23,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:47:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (7178)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.47  % (7171)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.47  % (7186)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.23/0.47  % (7186)Refutation not found, incomplete strategy% (7186)------------------------------
% 0.23/0.47  % (7186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (7186)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.47  
% 0.23/0.47  % (7186)Memory used [KB]: 10490
% 0.23/0.47  % (7186)Time elapsed: 0.056 s
% 0.23/0.47  % (7186)------------------------------
% 0.23/0.47  % (7186)------------------------------
% 0.23/0.49  % (7167)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.49  % (7167)Refutation not found, incomplete strategy% (7167)------------------------------
% 0.23/0.49  % (7167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (7167)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (7167)Memory used [KB]: 10618
% 0.23/0.49  % (7167)Time elapsed: 0.049 s
% 0.23/0.49  % (7167)------------------------------
% 0.23/0.49  % (7167)------------------------------
% 0.23/0.50  % (7174)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.50  % (7179)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (7179)Refutation not found, incomplete strategy% (7179)------------------------------
% 0.23/0.50  % (7179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (7179)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (7179)Memory used [KB]: 1535
% 0.23/0.50  % (7179)Time elapsed: 0.073 s
% 0.23/0.50  % (7179)------------------------------
% 0.23/0.50  % (7179)------------------------------
% 0.23/0.50  % (7170)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.51  % (7177)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.52  % (7185)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.23/0.52  % (7172)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.52  % (7185)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f106,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(trivial_inequality_removal,[],[f105])).
% 0.23/0.52  fof(f105,plain,(
% 0.23/0.52    k1_xboole_0 != k1_xboole_0),
% 0.23/0.52    inference(superposition,[],[f52,f97])).
% 0.23/0.52  fof(f97,plain,(
% 0.23/0.52    ( ! [X5] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X5)) )),
% 0.23/0.52    inference(resolution,[],[f91,f28])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.52  fof(f91,plain,(
% 0.23/0.52    ( ! [X1] : (v1_xboole_0(k9_relat_1(k1_xboole_0,X1))) )),
% 0.23/0.52    inference(subsumption_resolution,[],[f90,f31])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.23/0.52  fof(f90,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v1_xboole_0(k9_relat_1(k1_xboole_0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.23/0.52    inference(superposition,[],[f77,f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.23/0.52  fof(f77,plain,(
% 0.23/0.52    ( ! [X6,X5] : (v1_xboole_0(k7_relset_1(X5,k1_xboole_0,k1_xboole_0,X6))) )),
% 0.23/0.52    inference(resolution,[],[f69,f31])).
% 0.23/0.52  fof(f69,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(k7_relset_1(X0,k1_xboole_0,X1,X2))) )),
% 0.23/0.52    inference(forward_demodulation,[],[f64,f33])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.52    inference(equality_resolution,[],[f27])).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.52    inference(flattening,[],[f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.52    inference(nnf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.52  fof(f64,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(k7_relset_1(X0,k1_xboole_0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.23/0.52    inference(resolution,[],[f63,f29])).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.23/0.52  fof(f63,plain,(
% 0.23/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.23/0.52    inference(forward_demodulation,[],[f47,f48])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    k1_xboole_0 = sK2),
% 0.23/0.52    inference(resolution,[],[f40,f28])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    v1_xboole_0(sK2)),
% 0.23/0.52    inference(subsumption_resolution,[],[f36,f32])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    v1_xboole_0(k1_xboole_0)),
% 0.23/0.52    inference(cnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    v1_xboole_0(k1_xboole_0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.23/0.52  fof(f36,plain,(
% 0.23/0.52    v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.23/0.52    inference(resolution,[],[f35,f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f17])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.52    inference(forward_demodulation,[],[f22,f34])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.52    inference(equality_resolution,[],[f26])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f21])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.52    inference(cnf_transformation,[],[f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.23/0.52    inference(ennf_transformation,[],[f12])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.23/0.52  fof(f10,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.52    inference(negated_conjecture,[],[f9])).
% 0.23/0.52  fof(f9,conjecture,(
% 0.23/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2))) )),
% 0.23/0.52    inference(resolution,[],[f40,f30])).
% 0.23/0.52  fof(f52,plain,(
% 0.23/0.52    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)),
% 0.23/0.52    inference(forward_demodulation,[],[f46,f48])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    k1_xboole_0 != k9_relat_1(sK2,sK1)),
% 0.23/0.52    inference(subsumption_resolution,[],[f45,f35])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k9_relat_1(sK2,sK1)),
% 0.23/0.52    inference(forward_demodulation,[],[f44,f34])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    k1_xboole_0 != k9_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.23/0.52    inference(superposition,[],[f23,f24])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f19])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (7185)------------------------------
% 0.23/0.52  % (7185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (7185)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (7185)Memory used [KB]: 6140
% 0.23/0.52  % (7185)Time elapsed: 0.090 s
% 0.23/0.52  % (7185)------------------------------
% 0.23/0.52  % (7185)------------------------------
% 0.23/0.52  % (7183)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.52  % (7165)Success in time 0.143 s
%------------------------------------------------------------------------------
