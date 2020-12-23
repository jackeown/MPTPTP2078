%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 356 expanded)
%              Number of leaves         :   38 ( 149 expanded)
%              Depth                    :    9
%              Number of atoms          :  545 (1292 expanded)
%              Number of equality atoms :   48 (  98 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f114,f116,f119,f132,f134,f146,f154,f162,f167,f177,f183,f196,f211,f226,f233,f238,f246,f255,f262,f264,f275,f398,f401,f439])).

fof(f439,plain,
    ( spl3_20
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | spl3_20
    | ~ spl3_37 ),
    inference(resolution,[],[f429,f97])).

fof(f97,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    inference(resolution,[],[f80,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f429,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_20
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f232,f397])).

fof(f397,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl3_37
  <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f232,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl3_20
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f401,plain,
    ( ~ spl3_14
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl3_14
    | spl3_36 ),
    inference(resolution,[],[f376,f199])).

fof(f199,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(resolution,[],[f195,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f195,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_14
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f376,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl3_36
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

% (21478)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (21480)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (21473)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (21484)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (21468)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (21477)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (21476)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (21478)Refutation not found, incomplete strategy% (21478)------------------------------
% (21478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21478)Termination reason: Refutation not found, incomplete strategy

% (21478)Memory used [KB]: 11001
% (21478)Time elapsed: 0.085 s
% (21478)------------------------------
% (21478)------------------------------
fof(f398,plain,
    ( ~ spl3_22
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_36
    | ~ spl3_16
    | ~ spl3_15
    | spl3_37
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f381,f271,f395,f204,f208,f374,f103,f107,f241])).

fof(f241,plain,
    ( spl3_22
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f107,plain,
    ( spl3_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f103,plain,
    ( spl3_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f208,plain,
    ( spl3_16
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f204,plain,
    ( spl3_15
  <=> v2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f271,plain,
    ( spl3_25
  <=> sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f381,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ v2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_25 ),
    inference(superposition,[],[f120,f273])).

fof(f273,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f271])).

fof(f120,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f79,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f275,plain,
    ( ~ spl3_14
    | spl3_25
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f269,f223,f271,f193])).

fof(f223,plain,
    ( spl3_19
  <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f269,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_19 ),
    inference(superposition,[],[f72,f225])).

fof(f225,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f223])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f264,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl3_24 ),
    inference(resolution,[],[f261,f97])).

fof(f261,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl3_24
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f262,plain,
    ( ~ spl3_22
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_9
    | spl3_21 ),
    inference(avatar_split_clause,[],[f257,f235,f142,f259,f103,f107,f241])).

fof(f142,plain,
    ( spl3_9
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f235,plain,
    ( spl3_21
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f257,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_9
    | spl3_21 ),
    inference(forward_demodulation,[],[f256,f144])).

fof(f144,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f256,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_21 ),
    inference(superposition,[],[f237,f79])).

fof(f237,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f255,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_11
    | spl3_16 ),
    inference(resolution,[],[f210,f163])).

fof(f163,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f153,f161])).

fof(f161,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_11
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f153,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl3_10
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f210,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f246,plain,(
    spl3_22 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl3_22 ),
    inference(resolution,[],[f243,f90])).

fof(f90,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f71,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f45])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f243,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f241])).

fof(f238,plain,
    ( ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_14
    | ~ spl3_21
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f228,f159,f82,f235,f193,f208,f138,f107])).

fof(f138,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f228,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl3_1
    | ~ spl3_11 ),
    inference(superposition,[],[f165,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f165,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_1
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f84,f161])).

fof(f84,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f233,plain,
    ( ~ spl3_16
    | ~ spl3_14
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_20
    | spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f227,f159,f86,f230,f138,f107,f193,f208])).

fof(f86,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f227,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_2
    | ~ spl3_11 ),
    inference(superposition,[],[f164,f76])).

fof(f164,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl3_2
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f88,f161])).

fof(f88,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f226,plain,
    ( ~ spl3_16
    | ~ spl3_12
    | spl3_19
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f202,f193,f223,f174,f208])).

fof(f174,plain,
    ( spl3_12
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f202,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(resolution,[],[f195,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f211,plain,
    ( spl3_15
    | ~ spl3_16
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f197,f193,f180,f208,f204])).

fof(f180,plain,
    ( spl3_13
  <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f197,plain,
    ( ~ v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_14 ),
    inference(resolution,[],[f195,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f196,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_8
    | spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f191,f159,f193,f138,f111,f125,f107])).

fof(f125,plain,
    ( spl3_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( spl3_5
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f191,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f66,f161])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f183,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_8
    | spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f178,f159,f180,f138,f111,f125,f107])).

fof(f178,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f65,f161])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f177,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_8
    | spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f172,f159,f174,f138,f111,f125,f107])).

fof(f172,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f64,f161])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f167,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f140,f52])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f162,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | spl3_11 ),
    inference(avatar_split_clause,[],[f155,f159,f111,f125,f107])).

fof(f155,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f62,f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f154,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_5
    | spl3_10 ),
    inference(avatar_split_clause,[],[f147,f151,f111,f125,f107])).

fof(f147,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f146,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f136,f129,f142,f138])).

fof(f129,plain,
    ( spl3_7
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f136,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f72,f131])).

fof(f131,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f134,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f127,f50])).

fof(f50,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f127,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f121,f129,f125,f107])).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f67,f52])).

fof(f119,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f113,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f116,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f109,f49])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f109,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f114,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f99,f111,f107,f103])).

fof(f99,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f74,f52])).

fof(f89,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f53,f86,f82])).

fof(f53,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (21472)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (21474)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (21483)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (21481)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (21467)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (21470)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (21471)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (21469)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (21471)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f440,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f89,f114,f116,f119,f132,f134,f146,f154,f162,f167,f177,f183,f196,f211,f226,f233,f238,f246,f255,f262,f264,f275,f398,f401,f439])).
% 0.22/0.48  fof(f439,plain,(
% 0.22/0.48    spl3_20 | ~spl3_37),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f438])).
% 0.22/0.48  fof(f438,plain,(
% 0.22/0.48    $false | (spl3_20 | ~spl3_37)),
% 0.22/0.48    inference(resolution,[],[f429,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) )),
% 0.22/0.49    inference(resolution,[],[f80,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f55,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.49    inference(condensation,[],[f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.49  fof(f429,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl3_20 | ~spl3_37)),
% 0.22/0.49    inference(backward_demodulation,[],[f232,f397])).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl3_37),
% 0.22/0.49    inference(avatar_component_clause,[],[f395])).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    spl3_37 <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f230])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    spl3_20 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f401,plain,(
% 0.22/0.49    ~spl3_14 | spl3_36),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f399])).
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    $false | (~spl3_14 | spl3_36)),
% 0.22/0.49    inference(resolution,[],[f376,f199])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    v1_relat_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f195,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f193])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl3_14 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f376,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(sK1)) | spl3_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f374])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    spl3_36 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.49  % (21478)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (21480)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (21473)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (21484)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (21468)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (21477)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (21476)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (21478)Refutation not found, incomplete strategy% (21478)------------------------------
% 0.22/0.51  % (21478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21478)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21478)Memory used [KB]: 11001
% 0.22/0.51  % (21478)Time elapsed: 0.085 s
% 0.22/0.51  % (21478)------------------------------
% 0.22/0.51  % (21478)------------------------------
% 0.22/0.51  fof(f398,plain,(
% 0.22/0.51    ~spl3_22 | ~spl3_4 | ~spl3_3 | ~spl3_36 | ~spl3_16 | ~spl3_15 | spl3_37 | ~spl3_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f381,f271,f395,f204,f208,f374,f103,f107,f241])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    spl3_22 <=> v1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl3_4 <=> v1_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl3_3 <=> v2_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl3_16 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    spl3_15 <=> v2_funct_1(k2_funct_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    spl3_25 <=> sK0 = k1_relat_1(k2_funct_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.51  fof(f381,plain,(
% 0.22/0.51    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~v2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_25),
% 0.22/0.51    inference(superposition,[],[f120,f273])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~spl3_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f271])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(superposition,[],[f79,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f60,f54])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ~spl3_14 | spl3_25 | ~spl3_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f269,f223,f271,f193])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    spl3_19 <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_19),
% 0.22/0.51    inference(superposition,[],[f72,f225])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~spl3_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f223])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    spl3_24),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    $false | spl3_24),
% 0.22/0.51    inference(resolution,[],[f261,f97])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl3_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f259])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    spl3_24 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    ~spl3_22 | ~spl3_4 | ~spl3_3 | ~spl3_24 | ~spl3_9 | spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f257,f235,f142,f259,f103,f107,f241])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    spl3_9 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    spl3_21 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_9 | spl3_21)),
% 0.22/0.51    inference(forward_demodulation,[],[f256,f144])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK1) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f142])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_21),
% 0.22/0.51    inference(superposition,[],[f237,f79])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl3_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f235])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ~spl3_10 | ~spl3_11 | spl3_16),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f253])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    $false | (~spl3_10 | ~spl3_11 | spl3_16)),
% 0.22/0.51    inference(resolution,[],[f210,f163])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK1)) | (~spl3_10 | ~spl3_11)),
% 0.22/0.51    inference(backward_demodulation,[],[f153,f161])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f159])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    spl3_11 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f151])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    spl3_10 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ~v1_funct_1(k2_funct_1(sK1)) | spl3_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f208])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    spl3_22),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f245])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    $false | spl3_22),
% 0.22/0.51    inference(resolution,[],[f243,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f71,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ~v1_relat_1(sK1) | spl3_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f241])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_8 | ~spl3_16 | ~spl3_14 | ~spl3_21 | spl3_1 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f228,f159,f82,f235,f193,f208,f138,f107])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl3_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (spl3_1 | ~spl3_11)),
% 0.22/0.51    inference(superposition,[],[f165,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.51    inference(flattening,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (spl3_1 | ~spl3_11)),
% 0.22/0.51    inference(backward_demodulation,[],[f84,f161])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f82])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ~spl3_16 | ~spl3_14 | ~spl3_4 | ~spl3_8 | ~spl3_20 | spl3_2 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f227,f159,f86,f230,f138,f107,f193,f208])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl3_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | (spl3_2 | ~spl3_11)),
% 0.22/0.51    inference(superposition,[],[f164,f76])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | (spl3_2 | ~spl3_11)),
% 0.22/0.51    inference(backward_demodulation,[],[f88,f161])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    ~spl3_16 | ~spl3_12 | spl3_19 | ~spl3_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f202,f193,f223,f174,f208])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    spl3_12 <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.22/0.51    inference(resolution,[],[f195,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl3_15 | ~spl3_16 | ~spl3_13 | ~spl3_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f197,f193,f180,f208,f204])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    spl3_13 <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ~v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK1)) | v2_funct_1(k2_funct_1(sK1)) | ~spl3_14),
% 0.22/0.51    inference(resolution,[],[f195,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | ~spl3_5 | ~spl3_8 | spl3_14 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f191,f159,f193,f138,f111,f125,f107])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl3_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl3_5 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f66,f161])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | ~spl3_5 | ~spl3_8 | spl3_13 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f178,f159,f180,f138,f111,f125,f107])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    v3_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f65,f161])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | ~spl3_5 | ~spl3_8 | spl3_12 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f172,f159,f174,f138,f111,f125,f107])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f64,f161])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl3_8),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f166])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    $false | spl3_8),
% 0.22/0.51    inference(resolution,[],[f140,f52])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | ~spl3_5 | spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f159,f111,f125,f107])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f62,f52])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | ~spl3_5 | spl3_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f147,f151,f111,f125,f107])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f63,f52])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~spl3_8 | spl3_9 | ~spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f136,f129,f142,f138])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl3_7 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 0.22/0.51    inference(superposition,[],[f72,f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    spl3_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f133])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    $false | spl3_6),
% 0.22/0.51    inference(resolution,[],[f127,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ~v1_funct_2(sK1,sK0,sK0) | spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f129,f125,f107])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f67,f52])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    $false | spl3_5),
% 0.22/0.51    inference(resolution,[],[f113,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ~v3_funct_2(sK1,sK0,sK0) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f111])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    $false | spl3_4),
% 0.22/0.51    inference(resolution,[],[f109,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~v1_funct_1(sK1) | spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f107])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl3_3 | ~spl3_4 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f99,f111,f107,f103])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f74,f52])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f86,f82])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21471)------------------------------
% 0.22/0.51  % (21471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21471)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21471)Memory used [KB]: 6396
% 0.22/0.51  % (21471)Time elapsed: 0.067 s
% 0.22/0.51  % (21471)------------------------------
% 0.22/0.51  % (21471)------------------------------
% 0.22/0.51  % (21458)Success in time 0.149 s
%------------------------------------------------------------------------------
