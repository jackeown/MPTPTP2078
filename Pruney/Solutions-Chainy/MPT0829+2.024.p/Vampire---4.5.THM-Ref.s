%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 163 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  244 ( 431 expanded)
%              Number of equality atoms :   42 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f72,f74,f116,f118,f124,f365,f429,f479,f608])).

fof(f608,plain,
    ( spl3_1
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | spl3_1
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f600])).

fof(f600,plain,
    ( sK1 != sK1
    | spl3_1
    | ~ spl3_25 ),
    inference(superposition,[],[f107,f549])).

fof(f549,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f548,f173])).

fof(f173,plain,(
    sK1 = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f163,f33])).

fof(f33,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(f163,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_relat_1(X1),sK2)
      | k9_relat_1(k6_relat_1(k2_relat_1(sK2)),X1) = X1 ) ),
    inference(resolution,[],[f92,f121])).

% (23232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (23243)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (23232)Refutation not found, incomplete strategy% (23232)------------------------------
% (23232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23232)Termination reason: Refutation not found, incomplete strategy

% (23232)Memory used [KB]: 10618
% (23232)Time elapsed: 0.118 s
% (23232)------------------------------
% (23232)------------------------------
fof(f121,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2) ) ),
    inference(global_subsumption,[],[f32,f120])).

fof(f120,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK2))
      | ~ r1_tarski(k6_relat_1(X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f52,f103])).

fof(f103,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    inference(resolution,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f548,plain,
    ( k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f542,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f542,plain,
    ( k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ spl3_25 ),
    inference(superposition,[],[f87,f425])).

fof(f425,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl3_25
  <=> k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f87,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f107,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f55,f103])).

fof(f55,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f479,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | spl3_26 ),
    inference(resolution,[],[f428,f34])).

fof(f428,plain,
    ( ~ v1_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl3_26
  <=> v1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f429,plain,
    ( spl3_25
    | ~ spl3_26
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f420,f363,f427,f424])).

fof(f363,plain,
    ( spl3_21
  <=> ! [X22] :
        ( ~ v4_relat_1(X22,k2_relat_1(sK2))
        | ~ v1_relat_1(X22)
        | k7_relat_1(X22,sK1) = X22 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f420,plain,
    ( ~ v1_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ spl3_21 ),
    inference(resolution,[],[f364,f82])).

fof(f82,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f364,plain,
    ( ! [X22] :
        ( ~ v4_relat_1(X22,k2_relat_1(sK2))
        | ~ v1_relat_1(X22)
        | k7_relat_1(X22,sK1) = X22 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f363])).

fof(f365,plain,
    ( ~ spl3_3
    | spl3_21 ),
    inference(avatar_split_clause,[],[f347,f363,f67])).

fof(f67,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f347,plain,(
    ! [X22] :
      ( ~ v4_relat_1(X22,k2_relat_1(sK2))
      | k7_relat_1(X22,sK1) = X22
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X22) ) ),
    inference(resolution,[],[f196,f84])).

fof(f84,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f196,plain,(
    ! [X14,X15,X16] :
      ( ~ v4_relat_1(X14,k2_relat_1(X15))
      | ~ v5_relat_1(X15,X16)
      | k7_relat_1(X14,X16) = X14
      | ~ v1_relat_1(X15)
      | ~ v1_relat_1(X14) ) ),
    inference(resolution,[],[f102,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X2) = X0 ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X2) = X0 ) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f124,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f112,f32])).

fof(f112,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f115,f33])).

fof(f115,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_7
  <=> r1_tarski(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f116,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f108,f57,f114,f111])).

fof(f57,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f108,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(resolution,[],[f51,f58])).

fof(f58,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f71,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f70,f67])).

fof(f63,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f38,f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f59,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f31,f57,f54])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (23231)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (23231)Refutation not found, incomplete strategy% (23231)------------------------------
% 0.21/0.46  % (23231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (23231)Memory used [KB]: 6140
% 0.21/0.46  % (23231)Time elapsed: 0.054 s
% 0.21/0.46  % (23231)------------------------------
% 0.21/0.46  % (23231)------------------------------
% 0.21/0.47  % (23247)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.47  % (23247)Refutation not found, incomplete strategy% (23247)------------------------------
% 0.21/0.47  % (23247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23247)Memory used [KB]: 10618
% 0.21/0.47  % (23247)Time elapsed: 0.056 s
% 0.21/0.47  % (23247)------------------------------
% 0.21/0.47  % (23247)------------------------------
% 0.21/0.49  % (23234)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (23224)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (23235)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (23239)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.49  % (23234)Refutation not found, incomplete strategy% (23234)------------------------------
% 0.21/0.49  % (23234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23234)Memory used [KB]: 10618
% 0.21/0.49  % (23234)Time elapsed: 0.085 s
% 0.21/0.49  % (23234)------------------------------
% 0.21/0.49  % (23234)------------------------------
% 0.21/0.49  % (23228)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (23229)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (23238)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (23233)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (23244)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (23246)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (23237)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (23244)Refutation not found, incomplete strategy% (23244)------------------------------
% 0.21/0.50  % (23244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23244)Memory used [KB]: 6140
% 0.21/0.50  % (23244)Time elapsed: 0.099 s
% 0.21/0.50  % (23244)------------------------------
% 0.21/0.50  % (23244)------------------------------
% 0.21/0.51  % (23226)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (23240)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (23236)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (23227)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (23240)Refutation not found, incomplete strategy% (23240)------------------------------
% 0.21/0.51  % (23240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23240)Memory used [KB]: 1663
% 0.21/0.51  % (23240)Time elapsed: 0.095 s
% 0.21/0.51  % (23240)------------------------------
% 0.21/0.51  % (23240)------------------------------
% 0.21/0.51  % (23227)Refutation not found, incomplete strategy% (23227)------------------------------
% 0.21/0.51  % (23227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23227)Memory used [KB]: 10618
% 0.21/0.51  % (23227)Time elapsed: 0.094 s
% 0.21/0.51  % (23227)------------------------------
% 0.21/0.51  % (23227)------------------------------
% 0.21/0.51  % (23225)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (23245)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (23242)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (23230)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (23236)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f610,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f59,f72,f74,f116,f118,f124,f365,f429,f479,f608])).
% 0.21/0.52  fof(f608,plain,(
% 0.21/0.52    spl3_1 | ~spl3_25),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f607])).
% 0.21/0.52  fof(f607,plain,(
% 0.21/0.52    $false | (spl3_1 | ~spl3_25)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f600])).
% 0.21/0.52  fof(f600,plain,(
% 0.21/0.52    sK1 != sK1 | (spl3_1 | ~spl3_25)),
% 0.21/0.52    inference(superposition,[],[f107,f549])).
% 0.21/0.52  fof(f549,plain,(
% 0.21/0.52    sK1 = k2_relat_1(sK2) | ~spl3_25),
% 0.21/0.52    inference(forward_demodulation,[],[f548,f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    sK1 = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.21/0.52    inference(resolution,[],[f163,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(k6_relat_1(X1),sK2) | k9_relat_1(k6_relat_1(k2_relat_1(sK2)),X1) = X1) )),
% 0.21/0.52    inference(resolution,[],[f92,f121])).
% 0.21/0.52  % (23232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.34/0.52  % (23243)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.34/0.52  % (23232)Refutation not found, incomplete strategy% (23232)------------------------------
% 1.34/0.52  % (23232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.52  % (23232)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.52  
% 1.34/0.52  % (23232)Memory used [KB]: 10618
% 1.34/0.52  % (23232)Time elapsed: 0.118 s
% 1.34/0.52  % (23232)------------------------------
% 1.34/0.52  % (23232)------------------------------
% 1.34/0.53  fof(f121,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK2)) | ~r1_tarski(k6_relat_1(X0),sK2)) )),
% 1.34/0.53    inference(global_subsumption,[],[f32,f120])).
% 1.34/0.53  fof(f120,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK2)) | ~r1_tarski(k6_relat_1(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.34/0.53    inference(superposition,[],[f52,f103])).
% 1.34/0.53  fof(f103,plain,(
% 1.34/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.34/0.53    inference(resolution,[],[f48,f32])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(flattening,[],[f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f92,plain,(
% 1.34/0.53    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k9_relat_1(k6_relat_1(X1),X2) = X2) )),
% 1.34/0.53    inference(resolution,[],[f44,f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,axiom,(
% 1.34/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 1.34/0.53  fof(f548,plain,(
% 1.34/0.53    k2_relat_1(sK2) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | ~spl3_25),
% 1.34/0.53    inference(forward_demodulation,[],[f542,f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,axiom,(
% 1.34/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.34/0.53  fof(f542,plain,(
% 1.34/0.53    k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) | ~spl3_25),
% 1.34/0.53    inference(superposition,[],[f87,f425])).
% 1.34/0.53  fof(f425,plain,(
% 1.34/0.53    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | ~spl3_25),
% 1.34/0.53    inference(avatar_component_clause,[],[f424])).
% 1.34/0.53  fof(f424,plain,(
% 1.34/0.53    spl3_25 <=> k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.34/0.53  fof(f87,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.34/0.53    inference(resolution,[],[f40,f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.34/0.53  fof(f107,plain,(
% 1.34/0.53    sK1 != k2_relat_1(sK2) | spl3_1),
% 1.34/0.53    inference(superposition,[],[f55,f103])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    sK1 != k2_relset_1(sK0,sK1,sK2) | spl3_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f54])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    spl3_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.34/0.53  fof(f479,plain,(
% 1.34/0.53    spl3_26),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f478])).
% 1.34/0.53  fof(f478,plain,(
% 1.34/0.53    $false | spl3_26),
% 1.34/0.53    inference(resolution,[],[f428,f34])).
% 1.34/0.53  fof(f428,plain,(
% 1.34/0.53    ~v1_relat_1(k6_relat_1(k2_relat_1(sK2))) | spl3_26),
% 1.34/0.53    inference(avatar_component_clause,[],[f427])).
% 1.34/0.53  fof(f427,plain,(
% 1.34/0.53    spl3_26 <=> v1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.34/0.53  fof(f429,plain,(
% 1.34/0.53    spl3_25 | ~spl3_26 | ~spl3_21),
% 1.34/0.53    inference(avatar_split_clause,[],[f420,f363,f427,f424])).
% 1.34/0.53  fof(f363,plain,(
% 1.34/0.53    spl3_21 <=> ! [X22] : (~v4_relat_1(X22,k2_relat_1(sK2)) | ~v1_relat_1(X22) | k7_relat_1(X22,sK1) = X22)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.34/0.53  fof(f420,plain,(
% 1.34/0.53    ~v1_relat_1(k6_relat_1(k2_relat_1(sK2))) | k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | ~spl3_21),
% 1.34/0.53    inference(resolution,[],[f364,f82])).
% 1.34/0.53  fof(f82,plain,(
% 1.34/0.53    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 1.34/0.53    inference(resolution,[],[f49,f35])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,axiom,(
% 1.34/0.53    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.53  fof(f364,plain,(
% 1.34/0.53    ( ! [X22] : (~v4_relat_1(X22,k2_relat_1(sK2)) | ~v1_relat_1(X22) | k7_relat_1(X22,sK1) = X22) ) | ~spl3_21),
% 1.34/0.53    inference(avatar_component_clause,[],[f363])).
% 1.34/0.53  fof(f365,plain,(
% 1.34/0.53    ~spl3_3 | spl3_21),
% 1.34/0.53    inference(avatar_split_clause,[],[f347,f363,f67])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    spl3_3 <=> v1_relat_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.34/0.53  fof(f347,plain,(
% 1.34/0.53    ( ! [X22] : (~v4_relat_1(X22,k2_relat_1(sK2)) | k7_relat_1(X22,sK1) = X22 | ~v1_relat_1(sK2) | ~v1_relat_1(X22)) )),
% 1.34/0.53    inference(resolution,[],[f196,f84])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    v5_relat_1(sK2,sK1)),
% 1.34/0.53    inference(resolution,[],[f50,f32])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f28])).
% 1.34/0.53  fof(f196,plain,(
% 1.34/0.53    ( ! [X14,X15,X16] : (~v4_relat_1(X14,k2_relat_1(X15)) | ~v5_relat_1(X15,X16) | k7_relat_1(X14,X16) = X14 | ~v1_relat_1(X15) | ~v1_relat_1(X14)) )),
% 1.34/0.53    inference(resolution,[],[f102,f42])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.34/0.53  fof(f102,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~v4_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k7_relat_1(X0,X2) = X0) )),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f101])).
% 1.34/0.53  fof(f101,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k7_relat_1(X0,X2) = X0) )),
% 1.34/0.53    inference(resolution,[],[f43,f45])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(flattening,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 1.34/0.53  fof(f124,plain,(
% 1.34/0.53    spl3_6),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f122])).
% 1.34/0.53  fof(f122,plain,(
% 1.34/0.53    $false | spl3_6),
% 1.34/0.53    inference(resolution,[],[f112,f32])).
% 1.34/0.53  fof(f112,plain,(
% 1.34/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f111])).
% 1.34/0.53  fof(f111,plain,(
% 1.34/0.53    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.34/0.53  fof(f118,plain,(
% 1.34/0.53    spl3_7),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f117])).
% 1.34/0.53  fof(f117,plain,(
% 1.34/0.53    $false | spl3_7),
% 1.34/0.53    inference(resolution,[],[f115,f33])).
% 1.34/0.53  fof(f115,plain,(
% 1.34/0.53    ~r1_tarski(k6_relat_1(sK1),sK2) | spl3_7),
% 1.34/0.53    inference(avatar_component_clause,[],[f114])).
% 1.34/0.53  fof(f114,plain,(
% 1.34/0.53    spl3_7 <=> r1_tarski(k6_relat_1(sK1),sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.34/0.53  fof(f116,plain,(
% 1.34/0.53    ~spl3_6 | ~spl3_7 | spl3_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f108,f57,f114,f111])).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    spl3_2 <=> r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.34/0.53  fof(f108,plain,(
% 1.34/0.53    ~r1_tarski(k6_relat_1(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 1.34/0.53    inference(resolution,[],[f51,f58])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | spl3_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f57])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f30])).
% 1.34/0.53  fof(f74,plain,(
% 1.34/0.53    spl3_4),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f73])).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    $false | spl3_4),
% 1.34/0.53    inference(resolution,[],[f71,f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f70])).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    spl3_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    spl3_3 | ~spl3_4),
% 1.34/0.53    inference(avatar_split_clause,[],[f63,f70,f67])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.34/0.53    inference(resolution,[],[f38,f32])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    ~spl3_1 | ~spl3_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f31,f57,f54])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (23236)------------------------------
% 1.34/0.53  % (23236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (23236)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (23236)Memory used [KB]: 11129
% 1.34/0.53  % (23236)Time elapsed: 0.112 s
% 1.34/0.53  % (23236)------------------------------
% 1.34/0.53  % (23236)------------------------------
% 1.34/0.53  % (23241)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.34/0.53  % (23223)Success in time 0.174 s
%------------------------------------------------------------------------------
