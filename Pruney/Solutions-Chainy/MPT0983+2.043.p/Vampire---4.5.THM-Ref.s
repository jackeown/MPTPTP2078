%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:39 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 249 expanded)
%              Number of leaves         :   35 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  409 (1025 expanded)
%              Number of equality atoms :   44 (  57 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f135,f186,f203,f229,f232,f234,f259,f261,f264,f266,f271,f290,f303,f320,f324,f328,f353,f381])).

% (26524)Refutation not found, incomplete strategy% (26524)------------------------------
% (26524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26524)Termination reason: Refutation not found, incomplete strategy

% (26524)Memory used [KB]: 10874
% (26524)Time elapsed: 0.114 s
% (26524)------------------------------
% (26524)------------------------------
fof(f381,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f82,f130,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f85,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f85,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f69,f67])).

fof(f67,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f45,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f49,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f130,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

% (26514)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f82,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f353,plain,
    ( spl6_4
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f44,f339])).

fof(f339,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_4
    | ~ spl6_14 ),
    inference(superposition,[],[f134,f246])).

fof(f246,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f134,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f328,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl6_23 ),
    inference(subsumption_resolution,[],[f114,f319])).

fof(f319,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl6_23
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f114,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

% (26515)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f324,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl6_21 ),
    inference(subsumption_resolution,[],[f103,f310])).

fof(f310,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_21
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f320,plain,
    ( spl6_1
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f306,f299,f317,f308,f76])).

fof(f76,plain,
    ( spl6_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f299,plain,
    ( spl6_20
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f306,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | v2_funct_2(sK3,sK0)
    | ~ spl6_20 ),
    inference(superposition,[],[f71,f301])).

fof(f301,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f299])).

fof(f71,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f303,plain,
    ( ~ spl6_10
    | spl6_20
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f297,f287,f299,f212])).

fof(f212,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f287,plain,
    ( spl6_18
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f297,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_18 ),
    inference(superposition,[],[f57,f289])).

fof(f289,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f287])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f290,plain,
    ( spl6_18
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f282,f248,f212,f208,f252,f220,f216,f287])).

fof(f216,plain,
    ( spl6_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f220,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f252,plain,
    ( spl6_16
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f208,plain,
    ( spl6_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f248,plain,
    ( spl6_15
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f282,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f271,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f69,f258])).

fof(f258,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl6_17
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f266,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl6_16 ),
    inference(subsumption_resolution,[],[f42,f254])).

fof(f254,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f264,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl6_15 ),
    inference(subsumption_resolution,[],[f38,f250])).

fof(f250,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f38,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f261,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl6_12 ),
    inference(subsumption_resolution,[],[f43,f222])).

fof(f222,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f220])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f259,plain,
    ( spl6_2
    | spl6_14
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f242,f183,f256,f252,f220,f216,f248,f212,f208,f244,f80])).

% (26531)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f183,plain,
    ( spl6_8
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f242,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl6_8 ),
    inference(superposition,[],[f61,f185])).

fof(f185,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

% (26541)Termination reason: Refutation not found, incomplete strategy

% (26541)Memory used [KB]: 6396
% (26541)Time elapsed: 0.148 s
% (26541)------------------------------
% (26541)------------------------------
% (26532)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (26543)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f234,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl6_11 ),
    inference(subsumption_resolution,[],[f37,f218])).

fof(f218,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f232,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl6_10 ),
    inference(subsumption_resolution,[],[f39,f214])).

fof(f214,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f212])).

fof(f229,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl6_9 ),
    inference(subsumption_resolution,[],[f41,f210])).

fof(f210,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f208])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f203,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f41,f37,f39,f43,f181,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f181,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f186,plain,
    ( ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f175,f183,f179])).

fof(f175,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f165,f40])).

fof(f165,plain,(
    ! [X4,X3] :
      ( ~ r2_relset_1(X4,X4,X3,k6_partfun1(X4))
      | k6_partfun1(X4) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) ) ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

% (26542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f135,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f124,f132,f128])).

fof(f124,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f36,f80,f76])).

fof(f36,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (26517)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (26519)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (26541)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (26518)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.47/0.56  % (26527)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.56  % (26535)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.57  % (26516)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.47/0.57  % (26534)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.57  % (26540)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.47/0.57  % (26520)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.57  % (26524)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.47/0.58  % (26537)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.64/0.58  % (26529)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.64/0.58  % (26522)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.64/0.58  % (26541)Refutation not found, incomplete strategy% (26541)------------------------------
% 1.64/0.58  % (26541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (26536)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.64/0.59  % (26528)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.64/0.59  % (26527)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  fof(f382,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(avatar_sat_refutation,[],[f83,f135,f186,f203,f229,f232,f234,f259,f261,f264,f266,f271,f290,f303,f320,f324,f328,f353,f381])).
% 1.64/0.59  % (26524)Refutation not found, incomplete strategy% (26524)------------------------------
% 1.64/0.59  % (26524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (26524)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (26524)Memory used [KB]: 10874
% 1.64/0.59  % (26524)Time elapsed: 0.114 s
% 1.64/0.59  % (26524)------------------------------
% 1.64/0.59  % (26524)------------------------------
% 1.64/0.59  fof(f381,plain,(
% 1.64/0.59    spl6_2 | ~spl6_3),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f378])).
% 1.64/0.59  fof(f378,plain,(
% 1.64/0.59    $false | (spl6_2 | ~spl6_3)),
% 1.64/0.59    inference(unit_resulting_resolution,[],[f82,f130,f89])).
% 1.64/0.59  fof(f89,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 1.64/0.59    inference(superposition,[],[f85,f87])).
% 1.64/0.59  fof(f87,plain,(
% 1.64/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.64/0.59    inference(resolution,[],[f52,f51])).
% 1.64/0.59  fof(f51,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f1])).
% 1.64/0.59  fof(f1,axiom,(
% 1.64/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.64/0.59  fof(f52,plain,(
% 1.64/0.59    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f21])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.64/0.59    inference(ennf_transformation,[],[f3])).
% 1.64/0.59  fof(f3,axiom,(
% 1.64/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.64/0.59  fof(f85,plain,(
% 1.64/0.59    v2_funct_1(k1_xboole_0)),
% 1.64/0.59    inference(superposition,[],[f69,f67])).
% 1.64/0.59  fof(f67,plain,(
% 1.64/0.59    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.64/0.59    inference(definition_unfolding,[],[f45,f46])).
% 1.64/0.59  fof(f46,plain,(
% 1.64/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f14])).
% 1.64/0.59  fof(f14,axiom,(
% 1.64/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.64/0.60  fof(f45,plain,(
% 1.64/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.64/0.60    inference(cnf_transformation,[],[f4])).
% 1.64/0.60  fof(f4,axiom,(
% 1.64/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.64/0.60  fof(f69,plain,(
% 1.64/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.64/0.60    inference(definition_unfolding,[],[f49,f46])).
% 1.64/0.60  fof(f49,plain,(
% 1.64/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f5])).
% 1.64/0.60  fof(f5,axiom,(
% 1.64/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.64/0.60  fof(f130,plain,(
% 1.64/0.60    v1_xboole_0(sK2) | ~spl6_3),
% 1.64/0.60    inference(avatar_component_clause,[],[f128])).
% 1.64/0.60  fof(f128,plain,(
% 1.64/0.60    spl6_3 <=> v1_xboole_0(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.64/0.60  % (26514)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.64/0.60  fof(f82,plain,(
% 1.64/0.60    ~v2_funct_1(sK2) | spl6_2),
% 1.64/0.60    inference(avatar_component_clause,[],[f80])).
% 1.64/0.60  fof(f80,plain,(
% 1.64/0.60    spl6_2 <=> v2_funct_1(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.64/0.60  fof(f353,plain,(
% 1.64/0.60    spl6_4 | ~spl6_14),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f350])).
% 1.64/0.60  fof(f350,plain,(
% 1.64/0.60    $false | (spl6_4 | ~spl6_14)),
% 1.64/0.60    inference(subsumption_resolution,[],[f44,f339])).
% 1.64/0.60  fof(f339,plain,(
% 1.64/0.60    ~v1_xboole_0(k1_xboole_0) | (spl6_4 | ~spl6_14)),
% 1.64/0.60    inference(superposition,[],[f134,f246])).
% 1.64/0.60  fof(f246,plain,(
% 1.64/0.60    k1_xboole_0 = sK0 | ~spl6_14),
% 1.64/0.60    inference(avatar_component_clause,[],[f244])).
% 1.64/0.60  fof(f244,plain,(
% 1.64/0.60    spl6_14 <=> k1_xboole_0 = sK0),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.64/0.60  fof(f134,plain,(
% 1.64/0.60    ~v1_xboole_0(sK0) | spl6_4),
% 1.64/0.60    inference(avatar_component_clause,[],[f132])).
% 1.64/0.60  fof(f132,plain,(
% 1.64/0.60    spl6_4 <=> v1_xboole_0(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.64/0.60  fof(f44,plain,(
% 1.64/0.60    v1_xboole_0(k1_xboole_0)),
% 1.64/0.60    inference(cnf_transformation,[],[f2])).
% 1.64/0.60  fof(f2,axiom,(
% 1.64/0.60    v1_xboole_0(k1_xboole_0)),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.64/0.60  fof(f328,plain,(
% 1.64/0.60    spl6_23),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f325])).
% 1.64/0.60  fof(f325,plain,(
% 1.64/0.60    $false | spl6_23),
% 1.64/0.60    inference(subsumption_resolution,[],[f114,f319])).
% 1.64/0.60  fof(f319,plain,(
% 1.64/0.60    ~v5_relat_1(sK3,sK0) | spl6_23),
% 1.64/0.60    inference(avatar_component_clause,[],[f317])).
% 1.64/0.60  fof(f317,plain,(
% 1.64/0.60    spl6_23 <=> v5_relat_1(sK3,sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.64/0.60  fof(f114,plain,(
% 1.64/0.60    v5_relat_1(sK3,sK0)),
% 1.64/0.60    inference(resolution,[],[f59,f39])).
% 1.64/0.60  fof(f39,plain,(
% 1.64/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.64/0.60    inference(cnf_transformation,[],[f20])).
% 1.64/0.60  fof(f20,plain,(
% 1.64/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.64/0.60    inference(flattening,[],[f19])).
% 1.64/0.60  fof(f19,plain,(
% 1.64/0.60    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.64/0.60    inference(ennf_transformation,[],[f18])).
% 1.64/0.60  fof(f18,negated_conjecture,(
% 1.64/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.64/0.60    inference(negated_conjecture,[],[f17])).
% 1.64/0.60  fof(f17,conjecture,(
% 1.64/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.64/0.60  fof(f59,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f27])).
% 1.64/0.60  fof(f27,plain,(
% 1.64/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(ennf_transformation,[],[f7])).
% 1.64/0.60  % (26515)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.64/0.60  fof(f7,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.64/0.60  fof(f324,plain,(
% 1.64/0.60    spl6_21),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f321])).
% 1.64/0.60  fof(f321,plain,(
% 1.64/0.60    $false | spl6_21),
% 1.64/0.60    inference(subsumption_resolution,[],[f103,f310])).
% 1.64/0.60  fof(f310,plain,(
% 1.64/0.60    ~v1_relat_1(sK3) | spl6_21),
% 1.64/0.60    inference(avatar_component_clause,[],[f308])).
% 1.64/0.60  fof(f308,plain,(
% 1.64/0.60    spl6_21 <=> v1_relat_1(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.64/0.60  fof(f103,plain,(
% 1.64/0.60    v1_relat_1(sK3)),
% 1.64/0.60    inference(resolution,[],[f56,f39])).
% 1.64/0.60  fof(f56,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f25])).
% 1.64/0.60  fof(f25,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(ennf_transformation,[],[f6])).
% 1.64/0.60  fof(f6,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.64/0.60  fof(f320,plain,(
% 1.64/0.60    spl6_1 | ~spl6_21 | ~spl6_23 | ~spl6_20),
% 1.64/0.60    inference(avatar_split_clause,[],[f306,f299,f317,f308,f76])).
% 1.64/0.60  fof(f76,plain,(
% 1.64/0.60    spl6_1 <=> v2_funct_2(sK3,sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.64/0.60  fof(f299,plain,(
% 1.64/0.60    spl6_20 <=> sK0 = k2_relat_1(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.64/0.60  fof(f306,plain,(
% 1.64/0.60    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | v2_funct_2(sK3,sK0) | ~spl6_20),
% 1.64/0.60    inference(superposition,[],[f71,f301])).
% 1.64/0.60  fof(f301,plain,(
% 1.64/0.60    sK0 = k2_relat_1(sK3) | ~spl6_20),
% 1.64/0.60    inference(avatar_component_clause,[],[f299])).
% 1.64/0.60  fof(f71,plain,(
% 1.64/0.60    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 1.64/0.60    inference(equality_resolution,[],[f54])).
% 1.64/0.60  fof(f54,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f24])).
% 1.64/0.60  fof(f24,plain,(
% 1.64/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.60    inference(flattening,[],[f23])).
% 1.64/0.60  fof(f23,plain,(
% 1.64/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.64/0.60    inference(ennf_transformation,[],[f12])).
% 1.64/0.60  fof(f12,axiom,(
% 1.64/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.64/0.60  fof(f303,plain,(
% 1.64/0.60    ~spl6_10 | spl6_20 | ~spl6_18),
% 1.64/0.60    inference(avatar_split_clause,[],[f297,f287,f299,f212])).
% 1.64/0.60  fof(f212,plain,(
% 1.64/0.60    spl6_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.64/0.60  fof(f287,plain,(
% 1.64/0.60    spl6_18 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.64/0.60  fof(f297,plain,(
% 1.64/0.60    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_18),
% 1.64/0.60    inference(superposition,[],[f57,f289])).
% 1.64/0.60  fof(f289,plain,(
% 1.64/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl6_18),
% 1.64/0.60    inference(avatar_component_clause,[],[f287])).
% 1.64/0.60  fof(f57,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f26])).
% 1.64/0.60  fof(f26,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(ennf_transformation,[],[f9])).
% 1.64/0.60  fof(f9,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.64/0.60  fof(f290,plain,(
% 1.64/0.60    spl6_18 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_9 | ~spl6_10 | ~spl6_15),
% 1.64/0.60    inference(avatar_split_clause,[],[f282,f248,f212,f208,f252,f220,f216,f287])).
% 1.64/0.60  fof(f216,plain,(
% 1.64/0.60    spl6_11 <=> v1_funct_1(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.64/0.60  fof(f220,plain,(
% 1.64/0.60    spl6_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.64/0.60  fof(f252,plain,(
% 1.64/0.60    spl6_16 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.64/0.60  fof(f208,plain,(
% 1.64/0.60    spl6_9 <=> v1_funct_1(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.64/0.60  fof(f248,plain,(
% 1.64/0.60    spl6_15 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.64/0.60  fof(f282,plain,(
% 1.64/0.60    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.64/0.60    inference(resolution,[],[f60,f40])).
% 1.64/0.60  fof(f40,plain,(
% 1.64/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.64/0.60    inference(cnf_transformation,[],[f20])).
% 1.64/0.60  fof(f60,plain,(
% 1.64/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f29])).
% 1.64/0.60  fof(f29,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/0.60    inference(flattening,[],[f28])).
% 1.64/0.60  fof(f28,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/0.60    inference(ennf_transformation,[],[f15])).
% 1.64/0.60  fof(f15,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.64/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.64/0.60  fof(f271,plain,(
% 1.64/0.60    spl6_17),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f267])).
% 1.64/0.60  fof(f267,plain,(
% 1.64/0.60    $false | spl6_17),
% 1.64/0.60    inference(unit_resulting_resolution,[],[f69,f258])).
% 1.64/0.60  fof(f258,plain,(
% 1.64/0.60    ~v2_funct_1(k6_partfun1(sK0)) | spl6_17),
% 1.64/0.60    inference(avatar_component_clause,[],[f256])).
% 1.64/0.60  fof(f256,plain,(
% 1.64/0.60    spl6_17 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.64/0.60  fof(f266,plain,(
% 1.64/0.60    spl6_16),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f265])).
% 1.64/0.60  fof(f265,plain,(
% 1.64/0.60    $false | spl6_16),
% 1.64/0.60    inference(subsumption_resolution,[],[f42,f254])).
% 1.64/0.60  fof(f254,plain,(
% 1.64/0.60    ~v1_funct_2(sK2,sK0,sK1) | spl6_16),
% 1.64/0.60    inference(avatar_component_clause,[],[f252])).
% 1.64/0.60  fof(f42,plain,(
% 1.64/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.60    inference(cnf_transformation,[],[f20])).
% 1.64/0.60  fof(f264,plain,(
% 1.64/0.60    spl6_15),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f263])).
% 1.64/0.60  fof(f263,plain,(
% 1.64/0.60    $false | spl6_15),
% 1.64/0.60    inference(subsumption_resolution,[],[f38,f250])).
% 1.64/0.60  fof(f250,plain,(
% 1.64/0.60    ~v1_funct_2(sK3,sK1,sK0) | spl6_15),
% 1.64/0.60    inference(avatar_component_clause,[],[f248])).
% 1.64/0.60  fof(f38,plain,(
% 1.64/0.60    v1_funct_2(sK3,sK1,sK0)),
% 1.64/0.60    inference(cnf_transformation,[],[f20])).
% 1.64/0.60  fof(f261,plain,(
% 1.64/0.60    spl6_12),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f260])).
% 1.64/0.60  fof(f260,plain,(
% 1.64/0.60    $false | spl6_12),
% 1.64/0.60    inference(subsumption_resolution,[],[f43,f222])).
% 1.64/0.60  fof(f222,plain,(
% 1.64/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_12),
% 1.64/0.60    inference(avatar_component_clause,[],[f220])).
% 1.64/0.60  fof(f43,plain,(
% 1.64/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.60    inference(cnf_transformation,[],[f20])).
% 1.64/0.60  fof(f259,plain,(
% 1.64/0.60    spl6_2 | spl6_14 | ~spl6_9 | ~spl6_10 | ~spl6_15 | ~spl6_11 | ~spl6_12 | ~spl6_16 | ~spl6_17 | ~spl6_8),
% 1.64/0.60    inference(avatar_split_clause,[],[f242,f183,f256,f252,f220,f216,f248,f212,f208,f244,f80])).
% 1.64/0.60  % (26531)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.64/0.60  fof(f183,plain,(
% 1.64/0.60    spl6_8 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.64/0.60  fof(f242,plain,(
% 1.64/0.60    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl6_8),
% 1.64/0.60    inference(superposition,[],[f61,f185])).
% 1.64/0.60  fof(f185,plain,(
% 1.64/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl6_8),
% 1.64/0.60    inference(avatar_component_clause,[],[f183])).
% 1.64/0.60  fof(f61,plain,(
% 1.64/0.60    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f31])).
% 1.64/0.60  fof(f31,plain,(
% 1.64/0.60    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.64/0.60    inference(flattening,[],[f30])).
% 1.64/0.60  % (26541)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (26541)Memory used [KB]: 6396
% 1.64/0.60  % (26541)Time elapsed: 0.148 s
% 1.64/0.60  % (26541)------------------------------
% 1.64/0.60  % (26541)------------------------------
% 1.64/0.60  % (26532)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.64/0.61  % (26543)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.64/0.61  fof(f30,plain,(
% 1.64/0.61    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.64/0.61    inference(ennf_transformation,[],[f16])).
% 1.64/0.61  fof(f16,axiom,(
% 1.64/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.64/0.61  fof(f234,plain,(
% 1.64/0.61    spl6_11),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f233])).
% 1.64/0.61  fof(f233,plain,(
% 1.64/0.61    $false | spl6_11),
% 1.64/0.61    inference(subsumption_resolution,[],[f37,f218])).
% 1.64/0.61  fof(f218,plain,(
% 1.64/0.61    ~v1_funct_1(sK3) | spl6_11),
% 1.64/0.61    inference(avatar_component_clause,[],[f216])).
% 1.64/0.61  fof(f37,plain,(
% 1.64/0.61    v1_funct_1(sK3)),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f232,plain,(
% 1.64/0.61    spl6_10),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f231])).
% 1.64/0.61  fof(f231,plain,(
% 1.64/0.61    $false | spl6_10),
% 1.64/0.61    inference(subsumption_resolution,[],[f39,f214])).
% 1.64/0.61  fof(f214,plain,(
% 1.64/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_10),
% 1.64/0.61    inference(avatar_component_clause,[],[f212])).
% 1.64/0.61  fof(f229,plain,(
% 1.64/0.61    spl6_9),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f228])).
% 1.64/0.61  fof(f228,plain,(
% 1.64/0.61    $false | spl6_9),
% 1.64/0.61    inference(subsumption_resolution,[],[f41,f210])).
% 1.64/0.61  fof(f210,plain,(
% 1.64/0.61    ~v1_funct_1(sK2) | spl6_9),
% 1.64/0.61    inference(avatar_component_clause,[],[f208])).
% 1.64/0.61  fof(f41,plain,(
% 1.64/0.61    v1_funct_1(sK2)),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f203,plain,(
% 1.64/0.61    spl6_7),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f191])).
% 1.64/0.61  fof(f191,plain,(
% 1.64/0.61    $false | spl6_7),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f41,f37,f39,f43,f181,f66])).
% 1.64/0.61  fof(f66,plain,(
% 1.64/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f35])).
% 1.64/0.61  fof(f35,plain,(
% 1.64/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.64/0.61    inference(flattening,[],[f34])).
% 1.64/0.61  fof(f34,plain,(
% 1.64/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.64/0.61    inference(ennf_transformation,[],[f13])).
% 1.64/0.61  fof(f13,axiom,(
% 1.64/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.64/0.61  fof(f181,plain,(
% 1.64/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f179])).
% 1.64/0.61  fof(f179,plain,(
% 1.64/0.61    spl6_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.64/0.61  fof(f186,plain,(
% 1.64/0.61    ~spl6_7 | spl6_8),
% 1.64/0.61    inference(avatar_split_clause,[],[f175,f183,f179])).
% 1.64/0.61  fof(f175,plain,(
% 1.64/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.61    inference(resolution,[],[f165,f40])).
% 1.64/0.61  fof(f165,plain,(
% 1.64/0.61    ( ! [X4,X3] : (~r2_relset_1(X4,X4,X3,k6_partfun1(X4)) | k6_partfun1(X4) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))) )),
% 1.64/0.61    inference(resolution,[],[f64,f68])).
% 1.64/0.61  fof(f68,plain,(
% 1.64/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.64/0.61    inference(definition_unfolding,[],[f47,f46])).
% 1.64/0.61  fof(f47,plain,(
% 1.64/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f11])).
% 1.64/0.61  fof(f11,axiom,(
% 1.64/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.64/0.61  fof(f64,plain,(
% 1.64/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f33])).
% 1.64/0.61  % (26542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.64/0.61  fof(f33,plain,(
% 1.64/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.61    inference(flattening,[],[f32])).
% 1.64/0.61  fof(f32,plain,(
% 1.64/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.64/0.61    inference(ennf_transformation,[],[f10])).
% 1.64/0.61  fof(f10,axiom,(
% 1.64/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.64/0.61  fof(f135,plain,(
% 1.64/0.61    spl6_3 | ~spl6_4),
% 1.64/0.61    inference(avatar_split_clause,[],[f124,f132,f128])).
% 1.64/0.61  fof(f124,plain,(
% 1.64/0.61    ~v1_xboole_0(sK0) | v1_xboole_0(sK2)),
% 1.64/0.61    inference(resolution,[],[f53,f43])).
% 1.64/0.61  fof(f53,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f22])).
% 1.64/0.61  fof(f22,plain,(
% 1.64/0.61    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.64/0.61    inference(ennf_transformation,[],[f8])).
% 1.64/0.61  fof(f8,axiom,(
% 1.64/0.61    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.64/0.61  fof(f83,plain,(
% 1.64/0.61    ~spl6_1 | ~spl6_2),
% 1.64/0.61    inference(avatar_split_clause,[],[f36,f80,f76])).
% 1.64/0.61  fof(f36,plain,(
% 1.64/0.61    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  % SZS output end Proof for theBenchmark
% 1.64/0.61  % (26527)------------------------------
% 1.64/0.61  % (26527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (26527)Termination reason: Refutation
% 1.64/0.61  
% 1.64/0.61  % (26527)Memory used [KB]: 6396
% 1.64/0.61  % (26527)Time elapsed: 0.170 s
% 1.64/0.61  % (26527)------------------------------
% 1.64/0.61  % (26527)------------------------------
% 1.64/0.61  % (26513)Success in time 0.244 s
%------------------------------------------------------------------------------
