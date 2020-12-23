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
% DateTime   : Thu Dec  3 13:06:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 194 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :    6
%              Number of atoms          :  332 ( 637 expanded)
%              Number of equality atoms :   37 (  94 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30583)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f58,f62,f66,f98,f102,f106,f115,f119,f126,f136,f140,f145,f152,f158,f162,f185,f190,f212,f222,f241,f254])).

fof(f254,plain,
    ( ~ spl4_15
    | spl4_33
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl4_15
    | spl4_33
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f251,f211])).

fof(f211,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_33
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f251,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(superposition,[],[f97,f240])).

fof(f240,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_39
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f97,plain,
    ( ! [X0] : v1_partfun1(sK3(X0),X0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_15
  <=> ! [X0] : v1_partfun1(sK3(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f241,plain,
    ( spl4_39
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f163,f156,f124,f239])).

fof(f124,plain,
    ( spl4_21
  <=> m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f156,plain,
    ( spl4_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f163,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(resolution,[],[f157,f125])).

fof(f125,plain,
    ( m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f124])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f156])).

fof(f222,plain,
    ( spl4_5
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f167,f160,f100,f56])).

fof(f56,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f100,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f160,plain,
    ( spl4_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(resolution,[],[f161,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f161,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f160])).

fof(f212,plain,
    ( ~ spl4_33
    | ~ spl4_27
    | spl4_29
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f196,f188,f183,f156,f210])).

fof(f183,plain,
    ( spl4_29
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f188,plain,
    ( spl4_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f196,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_27
    | spl4_29
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f184,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_27
    | ~ spl4_30 ),
    inference(resolution,[],[f189,f157])).

fof(f189,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f188])).

fof(f184,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f190,plain,
    ( spl4_30
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f175,f160,f104,f100,f60,f188])).

fof(f60,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f104,plain,
    ( spl4_17
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f173,f105])).

fof(f105,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f104])).

fof(f173,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f61,f167])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f185,plain,
    ( ~ spl4_29
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f178,f53,f45,f183])).

fof(f45,plain,
    ( spl4_2
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f178,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f46,f54])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f46,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f162,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f154,f150,f60,f49,f160])).

fof(f49,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f150,plain,
    ( spl4_26
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f154,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f153,f61])).

fof(f153,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(resolution,[],[f151,f50])).

fof(f50,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f150])).

fof(f158,plain,
    ( spl4_27
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f147,f138,f64,f156])).

fof(f64,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f138,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(resolution,[],[f139,f65])).

fof(f65,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0 )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f138])).

fof(f152,plain,
    ( spl4_26
    | spl4_2
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f146,f143,f45,f150])).

fof(f143,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f146,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | spl4_2
    | ~ spl4_25 ),
    inference(resolution,[],[f144,f46])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl4_25
    | ~ spl4_1
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f141,f134,f41,f143])).

fof(f41,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | ~ spl4_23 ),
    inference(resolution,[],[f135,f42])).

fof(f42,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f134])).

fof(f140,plain,
    ( spl4_24
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f122,f117,f100,f138])).

fof(f117,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(resolution,[],[f118,f101])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f117])).

fof(f136,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f34,f134])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f126,plain,
    ( spl4_21
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f120,f113,f104,f124])).

fof(f113,plain,
    ( spl4_19
  <=> ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f120,plain,
    ( m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(superposition,[],[f114,f105])).

fof(f114,plain,
    ( ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f119,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f24,f117])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f115,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f25,f113])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_partfun1(X1,X0)
      & v8_relat_2(X1)
      & v4_relat_2(X1)
      & v3_relat_2(X1)
      & v1_relat_2(X1)
      & v5_relat_1(X1,X0)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_partfun1)).

fof(f106,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f38,f104])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f102,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f23,f100])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f98,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f33,f96])).

fof(f33,plain,(
    ! [X0] : v1_partfun1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f22,f64])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f60])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f58,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f15,f56,f53])).

fof(f15,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:58:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.42  % (30592)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.44  % (30584)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.44  % (30587)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.45  % (30592)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  % (30583)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.45  fof(f256,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f43,f47,f51,f58,f62,f66,f98,f102,f106,f115,f119,f126,f136,f140,f145,f152,f158,f162,f185,f190,f212,f222,f241,f254])).
% 0.19/0.45  fof(f254,plain,(
% 0.19/0.45    ~spl4_15 | spl4_33 | ~spl4_39),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f253])).
% 0.19/0.45  fof(f253,plain,(
% 0.19/0.45    $false | (~spl4_15 | spl4_33 | ~spl4_39)),
% 0.19/0.45    inference(subsumption_resolution,[],[f251,f211])).
% 0.19/0.45  fof(f211,plain,(
% 0.19/0.45    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl4_33),
% 0.19/0.45    inference(avatar_component_clause,[],[f210])).
% 0.19/0.45  fof(f210,plain,(
% 0.19/0.45    spl4_33 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.19/0.45  fof(f251,plain,(
% 0.19/0.45    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl4_15 | ~spl4_39)),
% 0.19/0.45    inference(superposition,[],[f97,f240])).
% 0.19/0.45  fof(f240,plain,(
% 0.19/0.45    k1_xboole_0 = sK3(k1_xboole_0) | ~spl4_39),
% 0.19/0.45    inference(avatar_component_clause,[],[f239])).
% 0.19/0.45  fof(f239,plain,(
% 0.19/0.45    spl4_39 <=> k1_xboole_0 = sK3(k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    ( ! [X0] : (v1_partfun1(sK3(X0),X0)) ) | ~spl4_15),
% 0.19/0.45    inference(avatar_component_clause,[],[f96])).
% 0.19/0.45  fof(f96,plain,(
% 0.19/0.45    spl4_15 <=> ! [X0] : v1_partfun1(sK3(X0),X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.45  fof(f241,plain,(
% 0.19/0.45    spl4_39 | ~spl4_21 | ~spl4_27),
% 0.19/0.45    inference(avatar_split_clause,[],[f163,f156,f124,f239])).
% 0.19/0.45  fof(f124,plain,(
% 0.19/0.45    spl4_21 <=> m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.45  fof(f156,plain,(
% 0.19/0.45    spl4_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.19/0.45  fof(f163,plain,(
% 0.19/0.45    k1_xboole_0 = sK3(k1_xboole_0) | (~spl4_21 | ~spl4_27)),
% 0.19/0.45    inference(resolution,[],[f157,f125])).
% 0.19/0.45  fof(f125,plain,(
% 0.19/0.45    m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_21),
% 0.19/0.45    inference(avatar_component_clause,[],[f124])).
% 0.19/0.45  fof(f157,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_27),
% 0.19/0.45    inference(avatar_component_clause,[],[f156])).
% 0.19/0.45  fof(f222,plain,(
% 0.19/0.45    spl4_5 | ~spl4_16 | ~spl4_28),
% 0.19/0.45    inference(avatar_split_clause,[],[f167,f160,f100,f56])).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    spl4_5 <=> k1_xboole_0 = sK1),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.45  fof(f100,plain,(
% 0.19/0.45    spl4_16 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.19/0.45  fof(f160,plain,(
% 0.19/0.45    spl4_28 <=> v1_xboole_0(sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.19/0.45  fof(f167,plain,(
% 0.19/0.45    k1_xboole_0 = sK1 | (~spl4_16 | ~spl4_28)),
% 0.19/0.45    inference(resolution,[],[f161,f101])).
% 0.19/0.45  fof(f101,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_16),
% 0.19/0.45    inference(avatar_component_clause,[],[f100])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    v1_xboole_0(sK1) | ~spl4_28),
% 0.19/0.45    inference(avatar_component_clause,[],[f160])).
% 0.19/0.45  fof(f212,plain,(
% 0.19/0.45    ~spl4_33 | ~spl4_27 | spl4_29 | ~spl4_30),
% 0.19/0.45    inference(avatar_split_clause,[],[f196,f188,f183,f156,f210])).
% 0.19/0.45  fof(f183,plain,(
% 0.19/0.45    spl4_29 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.19/0.45  fof(f188,plain,(
% 0.19/0.45    spl4_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.19/0.45  fof(f196,plain,(
% 0.19/0.45    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl4_27 | spl4_29 | ~spl4_30)),
% 0.19/0.45    inference(backward_demodulation,[],[f184,f191])).
% 0.19/0.45  fof(f191,plain,(
% 0.19/0.45    k1_xboole_0 = sK2 | (~spl4_27 | ~spl4_30)),
% 0.19/0.45    inference(resolution,[],[f189,f157])).
% 0.19/0.45  fof(f189,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_30),
% 0.19/0.45    inference(avatar_component_clause,[],[f188])).
% 0.19/0.45  fof(f184,plain,(
% 0.19/0.45    ~v1_partfun1(sK2,k1_xboole_0) | spl4_29),
% 0.19/0.45    inference(avatar_component_clause,[],[f183])).
% 0.19/0.45  fof(f190,plain,(
% 0.19/0.45    spl4_30 | ~spl4_6 | ~spl4_16 | ~spl4_17 | ~spl4_28),
% 0.19/0.45    inference(avatar_split_clause,[],[f175,f160,f104,f100,f60,f188])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.45  fof(f104,plain,(
% 0.19/0.45    spl4_17 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.45  fof(f175,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_16 | ~spl4_17 | ~spl4_28)),
% 0.19/0.45    inference(forward_demodulation,[],[f173,f105])).
% 0.19/0.45  fof(f105,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_17),
% 0.19/0.45    inference(avatar_component_clause,[],[f104])).
% 0.19/0.45  fof(f173,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_6 | ~spl4_16 | ~spl4_28)),
% 0.19/0.45    inference(backward_demodulation,[],[f61,f167])).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f60])).
% 0.19/0.45  fof(f185,plain,(
% 0.19/0.45    ~spl4_29 | spl4_2 | ~spl4_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f178,f53,f45,f183])).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    spl4_2 <=> v1_partfun1(sK2,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    spl4_4 <=> k1_xboole_0 = sK0),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.45  fof(f178,plain,(
% 0.19/0.45    ~v1_partfun1(sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.19/0.45    inference(backward_demodulation,[],[f46,f54])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    k1_xboole_0 = sK0 | ~spl4_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f53])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ~v1_partfun1(sK2,sK0) | spl4_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f45])).
% 0.19/0.45  fof(f162,plain,(
% 0.19/0.45    spl4_28 | ~spl4_3 | ~spl4_6 | ~spl4_26),
% 0.19/0.45    inference(avatar_split_clause,[],[f154,f150,f60,f49,f160])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.45  fof(f150,plain,(
% 0.19/0.45    spl4_26 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.19/0.45  fof(f154,plain,(
% 0.19/0.45    v1_xboole_0(sK1) | (~spl4_3 | ~spl4_6 | ~spl4_26)),
% 0.19/0.45    inference(subsumption_resolution,[],[f153,f61])).
% 0.19/0.45  fof(f153,plain,(
% 0.19/0.45    v1_xboole_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | ~spl4_26)),
% 0.19/0.45    inference(resolution,[],[f151,f50])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    v1_funct_2(sK2,sK0,sK1) | ~spl4_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f49])).
% 0.19/0.45  fof(f151,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_funct_2(sK2,sK0,X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl4_26),
% 0.19/0.45    inference(avatar_component_clause,[],[f150])).
% 0.19/0.45  fof(f158,plain,(
% 0.19/0.45    spl4_27 | ~spl4_7 | ~spl4_24),
% 0.19/0.45    inference(avatar_split_clause,[],[f147,f138,f64,f156])).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.45  fof(f138,plain,(
% 0.19/0.45    spl4_24 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.19/0.45  fof(f147,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl4_7 | ~spl4_24)),
% 0.19/0.45    inference(resolution,[],[f139,f65])).
% 0.19/0.45  fof(f65,plain,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f64])).
% 0.19/0.45  fof(f139,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) ) | ~spl4_24),
% 0.19/0.45    inference(avatar_component_clause,[],[f138])).
% 0.19/0.45  fof(f152,plain,(
% 0.19/0.45    spl4_26 | spl4_2 | ~spl4_25),
% 0.19/0.45    inference(avatar_split_clause,[],[f146,f143,f45,f150])).
% 0.19/0.45  fof(f143,plain,(
% 0.19/0.45    spl4_25 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.19/0.45  fof(f146,plain,(
% 0.19/0.45    ( ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (spl4_2 | ~spl4_25)),
% 0.19/0.45    inference(resolution,[],[f144,f46])).
% 0.19/0.45  fof(f144,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_25),
% 0.19/0.45    inference(avatar_component_clause,[],[f143])).
% 0.19/0.45  fof(f145,plain,(
% 0.19/0.45    spl4_25 | ~spl4_1 | ~spl4_23),
% 0.19/0.45    inference(avatar_split_clause,[],[f141,f134,f41,f143])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    spl4_1 <=> v1_funct_1(sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.45  fof(f134,plain,(
% 0.19/0.45    spl4_23 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.19/0.45  fof(f141,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | (~spl4_1 | ~spl4_23)),
% 0.19/0.45    inference(resolution,[],[f135,f42])).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    v1_funct_1(sK2) | ~spl4_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f41])).
% 0.19/0.45  fof(f135,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl4_23),
% 0.19/0.45    inference(avatar_component_clause,[],[f134])).
% 0.19/0.45  fof(f140,plain,(
% 0.19/0.45    spl4_24 | ~spl4_16 | ~spl4_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f122,f117,f100,f138])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    spl4_20 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.19/0.45  fof(f122,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | (~spl4_16 | ~spl4_20)),
% 0.19/0.45    inference(resolution,[],[f118,f101])).
% 0.19/0.45  fof(f118,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl4_20),
% 0.19/0.45    inference(avatar_component_clause,[],[f117])).
% 0.19/0.45  fof(f136,plain,(
% 0.19/0.45    spl4_23),
% 0.19/0.45    inference(avatar_split_clause,[],[f34,f134])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.45  fof(f126,plain,(
% 0.19/0.45    spl4_21 | ~spl4_17 | ~spl4_19),
% 0.19/0.45    inference(avatar_split_clause,[],[f120,f113,f104,f124])).
% 0.19/0.45  fof(f113,plain,(
% 0.19/0.45    spl4_19 <=> ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.45  fof(f120,plain,(
% 0.19/0.45    m1_subset_1(sK3(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_17 | ~spl4_19)),
% 0.19/0.45    inference(superposition,[],[f114,f105])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl4_19),
% 0.19/0.45    inference(avatar_component_clause,[],[f113])).
% 0.19/0.45  fof(f119,plain,(
% 0.19/0.45    spl4_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f24,f117])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    spl4_19),
% 0.19/0.45    inference(avatar_split_clause,[],[f25,f113])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0] : ? [X1] : (v1_partfun1(X1,X0) & v8_relat_2(X1) & v4_relat_2(X1) & v3_relat_2(X1) & v1_relat_2(X1) & v5_relat_1(X1,X0) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_partfun1)).
% 0.19/0.45  fof(f106,plain,(
% 0.19/0.45    spl4_17),
% 0.19/0.45    inference(avatar_split_clause,[],[f38,f104])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.45    inference(equality_resolution,[],[f37])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    spl4_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f100])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    spl4_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f33,f96])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X0] : (v1_partfun1(sK3(X0),X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f6])).
% 0.19/0.45  fof(f66,plain,(
% 0.19/0.45    spl4_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f22,f64])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.45  fof(f62,plain,(
% 0.19/0.45    spl4_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f20,f60])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.19/0.45    inference(flattening,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.19/0.45    inference(ennf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.19/0.45    inference(negated_conjecture,[],[f7])).
% 0.19/0.45  fof(f7,conjecture,(
% 0.19/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    spl4_4 | ~spl4_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f15,f56,f53])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    spl4_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f19,f49])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    ~spl4_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f21,f45])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ~v1_partfun1(sK2,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    spl4_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f18,f41])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    v1_funct_1(sK2)),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (30592)------------------------------
% 0.19/0.45  % (30592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (30592)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (30592)Memory used [KB]: 10746
% 0.19/0.45  % (30592)Time elapsed: 0.048 s
% 0.19/0.45  % (30592)------------------------------
% 0.19/0.45  % (30592)------------------------------
% 0.19/0.45  % (30582)Success in time 0.096 s
%------------------------------------------------------------------------------
