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
% DateTime   : Thu Dec  3 13:03:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 568 expanded)
%              Number of leaves         :    9 ( 110 expanded)
%              Depth                    :   20
%              Number of atoms          :  158 (2394 expanded)
%              Number of equality atoms :   68 ( 778 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f83])).

fof(f83,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f25,f82])).

fof(f82,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f21,f74])).

fof(f74,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f72,f25])).

fof(f72,plain,
    ( ~ r1_tarski(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f63,f67])).

fof(f67,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f50,f55])).

fof(f55,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

fof(f50,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f49,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f23,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f62,f59])).

fof(f59,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f56,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f62,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f58,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f58,plain,(
    ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    inference(backward_demodulation,[],[f57,f52])).

fof(f52,plain,(
    ! [X1] : k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1) ),
    inference(resolution,[],[f24,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f57,plain,(
    ~ r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(backward_demodulation,[],[f26,f51])).

fof(f51,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f24,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f26,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f116,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f115])).

fof(f115,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f87,f114])).

fof(f114,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f113,f80])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f76,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f24,f74])).

fof(f113,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f103,f42])).

fof(f103,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f75,f82])).

fof(f75,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f23,f74])).

fof(f87,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f79,f82])).

fof(f79,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f55,f74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (14457)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (14465)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (14465)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (14458)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (14453)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (14453)Refutation not found, incomplete strategy% (14453)------------------------------
% 0.20/0.47  % (14453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (14453)Memory used [KB]: 10618
% 0.20/0.47  % (14453)Time elapsed: 0.051 s
% 0.20/0.47  % (14453)------------------------------
% 0.20/0.47  % (14453)------------------------------
% 0.20/0.48  % (14459)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (14466)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f116,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f25,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    k1_xboole_0 = sK0),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.20/0.48    inference(superposition,[],[f21,f74])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f72,f25])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK0) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(superposition,[],[f63,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(superposition,[],[f50,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f24,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f49,f24])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.48    inference(resolution,[],[f23,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f62,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f56,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f24,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ~v1_relat_1(sK3) | ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.20/0.48    inference(resolution,[],[f58,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))),
% 0.20/0.48    inference(backward_demodulation,[],[f57,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X1] : (k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)) )),
% 0.20/0.48    inference(resolution,[],[f24,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ~r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.48    inference(backward_demodulation,[],[f26,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 0.20/0.48    inference(resolution,[],[f24,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    r1_tarski(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f63,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f87,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f113,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(forward_demodulation,[],[f76,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.48    inference(backward_demodulation,[],[f24,f74])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.48    inference(forward_demodulation,[],[f103,f42])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.48    inference(resolution,[],[f84,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f75,f82])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f23,f74])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f79,f82])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f55,f74])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (14465)------------------------------
% 0.20/0.48  % (14465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (14465)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (14465)Memory used [KB]: 1663
% 0.20/0.48  % (14465)Time elapsed: 0.064 s
% 0.20/0.48  % (14465)------------------------------
% 0.20/0.48  % (14465)------------------------------
% 0.20/0.48  % (14451)Success in time 0.118 s
%------------------------------------------------------------------------------
