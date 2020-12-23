%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 147 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 ( 898 expanded)
%              Number of equality atoms :   97 ( 441 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f74])).

fof(f74,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1) ),
    inference(backward_demodulation,[],[f42,f72])).

fof(f72,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(sK0) ),
    inference(forward_demodulation,[],[f71,f62])).

fof(f62,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f57,f56])).

fof(f56,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
      | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) )
    & k1_xboole_0 != sK1
    & v2_funct_1(sK2)
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

% (2813)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1)
          | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
        & k1_xboole_0 != X1
        & v2_funct_1(X2)
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
        | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) )
      & k1_xboole_0 != sK1
      & v2_funct_1(sK2)
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1)
        | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
      & k1_xboole_0 != X1
      & v2_funct_1(X2)
      & k2_relset_1(X0,X1,X2) = X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1)
        | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2)) )
      & k1_xboole_0 != X1
      & v2_funct_1(X2)
      & k2_relset_1(X0,X1,X2) = X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1 )
         => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
              & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f55,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f54,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f71,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f70,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f26,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f61,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f61,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f24,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f42,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1)
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(sK0) ),
    inference(definition_unfolding,[],[f28,f31,f31])).

fof(f31,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f28,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    inference(forward_demodulation,[],[f76,f64])).

fof(f64,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f58,f25])).

fof(f25,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f24,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f76,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f75,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f66,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (2805)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (2805)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (2810)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (2826)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f77,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    k6_relat_1(sK0) != k6_relat_1(sK0) | k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f42,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f71,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f57,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f55,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    (k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1) | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2))) & k1_xboole_0 != sK1 & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).
% 0.22/0.52  % (2813)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1) | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2))) & k1_xboole_0 != X1 & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1) | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2))) & k1_xboole_0 != sK1 & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1) | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2))) & k1_xboole_0 != X1 & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) != k6_partfun1(X1) | k6_partfun1(X0) != k5_relat_1(X2,k2_funct_1(X2))) & k1_xboole_0 != X1) & (v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f54,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(resolution,[],[f23,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(resolution,[],[f24,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f70,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f68,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f66,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f61,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f24,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) != k6_relat_1(sK1) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(sK0)),
% 0.22/0.52    inference(definition_unfolding,[],[f28,f31,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1) | k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f76,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2)),
% 0.22/0.52    inference(forward_demodulation,[],[f58,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f24,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f75,f22])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f69,f26])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f66,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (2805)------------------------------
% 0.22/0.52  % (2805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2805)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (2805)Memory used [KB]: 1791
% 0.22/0.52  % (2805)Time elapsed: 0.096 s
% 0.22/0.52  % (2805)------------------------------
% 0.22/0.52  % (2805)------------------------------
% 0.22/0.52  % (2804)Success in time 0.157 s
%------------------------------------------------------------------------------
