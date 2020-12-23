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
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 809 expanded)
%              Number of leaves         :    5 ( 197 expanded)
%              Depth                    :   19
%              Number of atoms          :  140 (3998 expanded)
%              Number of equality atoms :   77 (2064 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f117,f107])).

fof(f107,plain,(
    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f83,f99])).

fof(f99,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f17,f68])).

fof(f68,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(f54,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f53,f15])).

fof(f15,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f50,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f35,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f35,plain,(
    k8_relset_1(sK0,sK1,sK2,sK1) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f16,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f57,plain,(
    sK0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f37,f36])).

fof(f36,plain,(
    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k2_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    k7_relset_1(sK0,sK1,sK2,sK0) = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f16,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f16,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f37,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,k2_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f18,f34])).

fof(f18,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f57,f68])).

fof(f117,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f104,f116])).

fof(f116,plain,(
    k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f111,f102])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f70,f99])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f16,f68])).

fof(f111,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(resolution,[],[f101,f27])).

fof(f27,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK2,k1_xboole_0,X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X2,sK2,X2) ) ),
    inference(resolution,[],[f14,f25])).

fof(f25,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f101,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f69,f99])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f15,f68])).

fof(f104,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f73,f99])).

fof(f73,plain,(
    k8_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f35,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (1323)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (1340)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1323)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f83,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.48    inference(superposition,[],[f17,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    k1_xboole_0 = sK1),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    sK0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.48    inference(superposition,[],[f57,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f50,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(superposition,[],[f35,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k8_relset_1(sK0,sK1,sK2,sK1) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f16,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(superposition,[],[f37,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f33,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k7_relset_1(sK0,sK1,sK2,sK0) = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f16,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f16,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    sK0 != k8_relset_1(sK0,sK1,sK2,k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f18,f34])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f57,f68])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f104,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.48    inference(backward_demodulation,[],[f70,f99])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.48    inference(backward_demodulation,[],[f16,f68])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f101,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2] : (~v1_funct_2(sK2,k1_xboole_0,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X2,sK2,X2)) )),
% 0.21/0.48    inference(resolution,[],[f14,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(equality_resolution,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f69,f99])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f15,f68])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f73,f99])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k8_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f35,f68])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1323)------------------------------
% 0.21/0.48  % (1323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1323)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1323)Memory used [KB]: 1663
% 0.21/0.48  % (1323)Time elapsed: 0.065 s
% 0.21/0.48  % (1323)------------------------------
% 0.21/0.48  % (1323)------------------------------
% 0.21/0.48  % (1318)Success in time 0.119 s
%------------------------------------------------------------------------------
