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
% DateTime   : Thu Dec  3 13:02:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 281 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  486 (1000 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f86,f91,f114,f119,f126,f133,f138,f149,f161,f172,f176,f181,f187,f210,f235,f384,f389,f420,f478,f529])).

fof(f529,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | spl5_36
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | spl5_36
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f527,f65])).

fof(f65,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f527,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | spl5_36
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f526,f113])).

fof(f113,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f526,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl5_2
    | ~ spl5_10
    | spl5_36
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f525,f383])).

fof(f383,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | spl5_36 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl5_36
  <=> v5_relat_1(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f525,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_48 ),
    inference(superposition,[],[f477,f194])).

fof(f194,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(resolution,[],[f97,f118])).

fof(f118,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f97,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | k1_partfun1(X10,X11,X13,X14,sK3,X12) = k5_relat_1(sK3,X12) )
    | ~ spl5_2 ),
    inference(resolution,[],[f70,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f70,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f477,plain,
    ( v5_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f475])).

% (21966)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (21967)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (21972)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (21974)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f475,plain,
    ( spl5_48
  <=> v5_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f478,plain,
    ( spl5_48
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f427,f417,f475])).

fof(f417,plain,
    ( spl5_39
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f427,plain,
    ( v5_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)
    | ~ spl5_39 ),
    inference(resolution,[],[f419,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f419,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f417])).

fof(f420,plain,
    ( spl5_39
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f281,f116,f111,f68,f63,f417])).

fof(f281,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f238,f113])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(resolution,[],[f202,f65])).

fof(f202,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k1_partfun1(sK0,sK1,X1,X2,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) )
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(resolution,[],[f96,f118])).

fof(f96,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | m1_subset_1(k1_partfun1(X5,X6,X8,X9,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(X5,X9))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f389,plain,
    ( ~ spl5_17
    | ~ spl5_18
    | spl5_35 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl5_17
    | ~ spl5_18
    | spl5_35 ),
    inference(subsumption_resolution,[],[f387,f166])).

fof(f166,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f387,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_17
    | spl5_35 ),
    inference(subsumption_resolution,[],[f385,f159])).

fof(f159,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_17
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f385,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl5_35 ),
    inference(resolution,[],[f379,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f379,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl5_35
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f384,plain,
    ( ~ spl5_35
    | ~ spl5_36
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22
    | spl5_24 ),
    inference(avatar_split_clause,[],[f294,f232,f207,f169,f165,f158,f381,f377])).

fof(f169,plain,
    ( spl5_19
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f207,plain,
    ( spl5_22
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f232,plain,
    ( spl5_24
  <=> v2_funct_2(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f294,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22
    | spl5_24 ),
    inference(subsumption_resolution,[],[f293,f159])).

fof(f293,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22
    | spl5_24 ),
    inference(subsumption_resolution,[],[f292,f234])).

fof(f234,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f292,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(sK4)
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(superposition,[],[f221,f209])).

fof(f209,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f207])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k5_relat_1(sK3,X0),k9_relat_1(X0,sK1))
        | ~ v1_relat_1(k5_relat_1(sK3,X0))
        | v2_funct_2(k5_relat_1(sK3,X0),k9_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(superposition,[],[f61,f220])).

fof(f220,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f177,f171])).

fof(f171,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,k2_relat_1(sK3)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f166,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f61,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f235,plain,
    ( ~ spl5_24
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(avatar_split_clause,[],[f230,f135,f116,f111,f68,f63,f232])).

fof(f135,plain,
    ( spl5_13
  <=> v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f230,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f229,f65])).

fof(f229,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_funct_1(sK4)
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f228,f113])).

fof(f228,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl5_2
    | ~ spl5_10
    | spl5_13 ),
    inference(superposition,[],[f137,f194])).

fof(f137,plain,
    ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f210,plain,
    ( spl5_22
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f193,f184,f158,f154,f207])).

fof(f154,plain,
    ( spl5_16
  <=> sK4 = k7_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f184,plain,
    ( spl5_20
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f193,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f192,f186])).

fof(f186,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f192,plain,
    ( k2_relat_1(sK4) = k9_relat_1(sK4,sK1)
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f191,f159])).

fof(f191,plain,
    ( k2_relat_1(sK4) = k9_relat_1(sK4,sK1)
    | ~ v1_relat_1(sK4)
    | ~ spl5_16 ),
    inference(superposition,[],[f49,f156])).

fof(f156,plain,
    ( sK4 = k7_relat_1(sK4,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f187,plain,
    ( ~ spl5_17
    | spl5_20
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f182,f130,f88,f184,f158])).

fof(f88,plain,
    ( spl5_6
  <=> v2_funct_2(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f130,plain,
    ( spl5_12
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f182,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f109,f132])).

fof(f132,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f109,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_6 ),
    inference(resolution,[],[f90,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,
    ( v2_funct_2(sK4,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f181,plain,
    ( ~ spl5_9
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl5_9
    | spl5_17 ),
    inference(resolution,[],[f163,f113])).

fof(f163,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_17 ),
    inference(resolution,[],[f160,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f160,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f176,plain,
    ( ~ spl5_10
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl5_10
    | spl5_18 ),
    inference(resolution,[],[f173,f118])).

fof(f173,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_18 ),
    inference(resolution,[],[f167,f55])).

fof(f167,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f172,plain,
    ( ~ spl5_18
    | spl5_19
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f162,f146,f83,f169,f165])).

fof(f83,plain,
    ( spl5_5
  <=> v2_funct_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f146,plain,
    ( spl5_15
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f162,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f108,f148])).

fof(f148,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f108,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | sK1 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f85,f53])).

fof(f85,plain,
    ( v2_funct_2(sK3,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f161,plain,
    ( spl5_16
    | ~ spl5_17
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f139,f123,f158,f154])).

fof(f123,plain,
    ( spl5_11
  <=> v4_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f139,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f125,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f125,plain,
    ( v4_relat_1(sK4,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f149,plain,
    ( spl5_15
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f128,f116,f146])).

fof(f128,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f118,f57])).

fof(f138,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f39,f135])).

fof(f39,plain,(
    ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X4,X1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X4,X1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_2(X4,X1,X2)
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_2(X4,X1,X2)
                    & v1_funct_1(X4) )
                 => ( ( v2_funct_2(X4,X2)
                      & v2_funct_2(X3,X1) )
                   => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_funct_2)).

fof(f133,plain,
    ( spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f121,f111,f130])).

fof(f121,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f113,f57])).

fof(f126,plain,
    ( spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f120,f111,f123])).

fof(f120,plain,
    ( v4_relat_1(sK4,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f114,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f36,f111])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    v2_funct_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (21961)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (21969)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (21970)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (21963)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (21962)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (21956)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (21971)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (21960)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (21965)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (21957)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (21973)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (21964)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (21976)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (21975)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (21957)Refutation not found, incomplete strategy% (21957)------------------------------
% 0.20/0.51  % (21957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21957)Memory used [KB]: 10618
% 0.20/0.51  % (21957)Time elapsed: 0.101 s
% 0.20/0.51  % (21957)------------------------------
% 0.20/0.51  % (21957)------------------------------
% 0.20/0.51  % (21976)Refutation not found, incomplete strategy% (21976)------------------------------
% 0.20/0.51  % (21976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21976)Memory used [KB]: 10618
% 0.20/0.51  % (21976)Time elapsed: 0.104 s
% 0.20/0.51  % (21976)------------------------------
% 0.20/0.51  % (21976)------------------------------
% 0.20/0.51  % (21958)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (21959)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (21968)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (21959)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f530,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f66,f71,f86,f91,f114,f119,f126,f133,f138,f149,f161,f172,f176,f181,f187,f210,f235,f384,f389,f420,f478,f529])).
% 0.20/0.52  fof(f529,plain,(
% 0.20/0.52    ~spl5_1 | ~spl5_2 | ~spl5_9 | ~spl5_10 | spl5_36 | ~spl5_48),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f528])).
% 0.20/0.52  fof(f528,plain,(
% 0.20/0.52    $false | (~spl5_1 | ~spl5_2 | ~spl5_9 | ~spl5_10 | spl5_36 | ~spl5_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f527,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    v1_funct_1(sK4) | ~spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl5_1 <=> v1_funct_1(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f527,plain,(
% 0.20/0.52    ~v1_funct_1(sK4) | (~spl5_2 | ~spl5_9 | ~spl5_10 | spl5_36 | ~spl5_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f526,f113])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f111])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl5_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.52  fof(f526,plain,(
% 0.20/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | (~spl5_2 | ~spl5_10 | spl5_36 | ~spl5_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f525,f383])).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | spl5_36),
% 0.20/0.52    inference(avatar_component_clause,[],[f381])).
% 0.20/0.52  fof(f381,plain,(
% 0.20/0.52    spl5_36 <=> v5_relat_1(k5_relat_1(sK3,sK4),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.52  fof(f525,plain,(
% 0.20/0.52    v5_relat_1(k5_relat_1(sK3,sK4),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | (~spl5_2 | ~spl5_10 | ~spl5_48)),
% 0.20/0.52    inference(superposition,[],[f477,f194])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0)) ) | (~spl5_2 | ~spl5_10)),
% 0.20/0.52    inference(resolution,[],[f97,f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f116])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl5_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X14,X12,X10,X13,X11] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | k1_partfun1(X10,X11,X13,X14,sK3,X12) = k5_relat_1(sK3,X12)) ) | ~spl5_2),
% 0.20/0.52    inference(resolution,[],[f70,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    v1_funct_1(sK3) | ~spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl5_2 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f477,plain,(
% 0.20/0.52    v5_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) | ~spl5_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f475])).
% 0.20/0.52  % (21966)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (21967)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (21972)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (21974)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.55  fof(f475,plain,(
% 0.20/0.55    spl5_48 <=> v5_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.20/0.55  fof(f478,plain,(
% 0.20/0.55    spl5_48 | ~spl5_39),
% 0.20/0.55    inference(avatar_split_clause,[],[f427,f417,f475])).
% 0.20/0.55  fof(f417,plain,(
% 0.20/0.55    spl5_39 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.55  fof(f427,plain,(
% 0.20/0.55    v5_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) | ~spl5_39),
% 0.20/0.55    inference(resolution,[],[f419,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.55  fof(f419,plain,(
% 0.20/0.55    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_39),
% 0.20/0.55    inference(avatar_component_clause,[],[f417])).
% 0.20/0.55  fof(f420,plain,(
% 0.20/0.55    spl5_39 | ~spl5_1 | ~spl5_2 | ~spl5_9 | ~spl5_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f281,f116,f111,f68,f63,f417])).
% 0.20/0.55  fof(f281,plain,(
% 0.20/0.55    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_1 | ~spl5_2 | ~spl5_9 | ~spl5_10)),
% 0.20/0.55    inference(resolution,[],[f238,f113])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) ) | (~spl5_1 | ~spl5_2 | ~spl5_10)),
% 0.20/0.55    inference(resolution,[],[f202,f65])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k1_partfun1(sK0,sK1,X1,X2,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))) ) | (~spl5_2 | ~spl5_10)),
% 0.20/0.55    inference(resolution,[],[f96,f118])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | m1_subset_1(k1_partfun1(X5,X6,X8,X9,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(X5,X9)))) ) | ~spl5_2),
% 0.20/0.55    inference(resolution,[],[f70,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.55  fof(f389,plain,(
% 0.20/0.55    ~spl5_17 | ~spl5_18 | spl5_35),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f388])).
% 0.20/0.55  fof(f388,plain,(
% 0.20/0.55    $false | (~spl5_17 | ~spl5_18 | spl5_35)),
% 0.20/0.55    inference(subsumption_resolution,[],[f387,f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    v1_relat_1(sK3) | ~spl5_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f165])).
% 0.20/0.55  fof(f165,plain,(
% 0.20/0.55    spl5_18 <=> v1_relat_1(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.55  fof(f387,plain,(
% 0.20/0.55    ~v1_relat_1(sK3) | (~spl5_17 | spl5_35)),
% 0.20/0.55    inference(subsumption_resolution,[],[f385,f159])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    v1_relat_1(sK4) | ~spl5_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f158])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    spl5_17 <=> v1_relat_1(sK4)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.55  fof(f385,plain,(
% 0.20/0.55    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl5_35),
% 0.20/0.55    inference(resolution,[],[f379,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.55  fof(f379,plain,(
% 0.20/0.55    ~v1_relat_1(k5_relat_1(sK3,sK4)) | spl5_35),
% 0.20/0.55    inference(avatar_component_clause,[],[f377])).
% 0.20/0.55  fof(f377,plain,(
% 0.20/0.55    spl5_35 <=> v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.20/0.55  fof(f384,plain,(
% 0.20/0.55    ~spl5_35 | ~spl5_36 | ~spl5_17 | ~spl5_18 | ~spl5_19 | ~spl5_22 | spl5_24),
% 0.20/0.55    inference(avatar_split_clause,[],[f294,f232,f207,f169,f165,f158,f381,f377])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    spl5_19 <=> sK1 = k2_relat_1(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    spl5_22 <=> sK2 = k9_relat_1(sK4,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    spl5_24 <=> v2_funct_2(k5_relat_1(sK3,sK4),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | (~spl5_17 | ~spl5_18 | ~spl5_19 | ~spl5_22 | spl5_24)),
% 0.20/0.55    inference(subsumption_resolution,[],[f293,f159])).
% 0.20/0.55  fof(f293,plain,(
% 0.20/0.55    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK4) | (~spl5_18 | ~spl5_19 | ~spl5_22 | spl5_24)),
% 0.20/0.55    inference(subsumption_resolution,[],[f292,f234])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    ~v2_funct_2(k5_relat_1(sK3,sK4),sK2) | spl5_24),
% 0.20/0.55    inference(avatar_component_clause,[],[f232])).
% 0.20/0.55  fof(f292,plain,(
% 0.20/0.55    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | v2_funct_2(k5_relat_1(sK3,sK4),sK2) | ~v1_relat_1(sK4) | (~spl5_18 | ~spl5_19 | ~spl5_22)),
% 0.20/0.55    inference(superposition,[],[f221,f209])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    sK2 = k9_relat_1(sK4,sK1) | ~spl5_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f207])).
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    ( ! [X0] : (~v5_relat_1(k5_relat_1(sK3,X0),k9_relat_1(X0,sK1)) | ~v1_relat_1(k5_relat_1(sK3,X0)) | v2_funct_2(k5_relat_1(sK3,X0),k9_relat_1(X0,sK1)) | ~v1_relat_1(X0)) ) | (~spl5_18 | ~spl5_19)),
% 0.20/0.55    inference(superposition,[],[f61,f220])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    ( ! [X0] : (k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1) | ~v1_relat_1(X0)) ) | (~spl5_18 | ~spl5_19)),
% 0.20/0.55    inference(forward_demodulation,[],[f177,f171])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK3) | ~spl5_19),
% 0.20/0.55    inference(avatar_component_clause,[],[f169])).
% 0.20/0.55  fof(f177,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,k2_relat_1(sK3))) ) | ~spl5_18),
% 0.20/0.55    inference(resolution,[],[f166,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    ~spl5_24 | ~spl5_1 | ~spl5_2 | ~spl5_9 | ~spl5_10 | spl5_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f230,f135,f116,f111,f68,f63,f232])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl5_13 <=> v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ~v2_funct_2(k5_relat_1(sK3,sK4),sK2) | (~spl5_1 | ~spl5_2 | ~spl5_9 | ~spl5_10 | spl5_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f229,f65])).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    ~v2_funct_2(k5_relat_1(sK3,sK4),sK2) | ~v1_funct_1(sK4) | (~spl5_2 | ~spl5_9 | ~spl5_10 | spl5_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f228,f113])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    ~v2_funct_2(k5_relat_1(sK3,sK4),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | (~spl5_2 | ~spl5_10 | spl5_13)),
% 0.20/0.55    inference(superposition,[],[f137,f194])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) | spl5_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f135])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    spl5_22 | ~spl5_16 | ~spl5_17 | ~spl5_20),
% 0.20/0.55    inference(avatar_split_clause,[],[f193,f184,f158,f154,f207])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    spl5_16 <=> sK4 = k7_relat_1(sK4,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    spl5_20 <=> sK2 = k2_relat_1(sK4)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.55  fof(f193,plain,(
% 0.20/0.55    sK2 = k9_relat_1(sK4,sK1) | (~spl5_16 | ~spl5_17 | ~spl5_20)),
% 0.20/0.55    inference(forward_demodulation,[],[f192,f186])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    sK2 = k2_relat_1(sK4) | ~spl5_20),
% 0.20/0.55    inference(avatar_component_clause,[],[f184])).
% 0.20/0.55  fof(f192,plain,(
% 0.20/0.55    k2_relat_1(sK4) = k9_relat_1(sK4,sK1) | (~spl5_16 | ~spl5_17)),
% 0.20/0.55    inference(subsumption_resolution,[],[f191,f159])).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    k2_relat_1(sK4) = k9_relat_1(sK4,sK1) | ~v1_relat_1(sK4) | ~spl5_16),
% 0.20/0.55    inference(superposition,[],[f49,f156])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    sK4 = k7_relat_1(sK4,sK1) | ~spl5_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f154])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ~spl5_17 | spl5_20 | ~spl5_6 | ~spl5_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f182,f130,f88,f184,f158])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    spl5_6 <=> v2_funct_2(sK4,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    spl5_12 <=> v5_relat_1(sK4,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl5_6 | ~spl5_12)),
% 0.20/0.55    inference(subsumption_resolution,[],[f109,f132])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    v5_relat_1(sK4,sK2) | ~spl5_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f130])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ~v5_relat_1(sK4,sK2) | sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl5_6),
% 0.20/0.55    inference(resolution,[],[f90,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    v2_funct_2(sK4,sK2) | ~spl5_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f88])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    ~spl5_9 | spl5_17),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    $false | (~spl5_9 | spl5_17)),
% 0.20/0.55    inference(resolution,[],[f163,f113])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_17),
% 0.20/0.55    inference(resolution,[],[f160,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f160,plain,(
% 0.20/0.55    ~v1_relat_1(sK4) | spl5_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f158])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ~spl5_10 | spl5_18),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.55  fof(f175,plain,(
% 0.20/0.55    $false | (~spl5_10 | spl5_18)),
% 0.20/0.55    inference(resolution,[],[f173,f118])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_18),
% 0.20/0.55    inference(resolution,[],[f167,f55])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    ~v1_relat_1(sK3) | spl5_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f165])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    ~spl5_18 | spl5_19 | ~spl5_5 | ~spl5_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f162,f146,f83,f169,f165])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    spl5_5 <=> v2_funct_2(sK3,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    spl5_15 <=> v5_relat_1(sK3,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl5_5 | ~spl5_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f108,f148])).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    v5_relat_1(sK3,sK1) | ~spl5_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f146])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ~v5_relat_1(sK3,sK1) | sK1 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl5_5),
% 0.20/0.55    inference(resolution,[],[f85,f53])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    v2_funct_2(sK3,sK1) | ~spl5_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f83])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    spl5_16 | ~spl5_17 | ~spl5_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f139,f123,f158,f154])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl5_11 <=> v4_relat_1(sK4,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK1) | ~spl5_11),
% 0.20/0.55    inference(resolution,[],[f125,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    v4_relat_1(sK4,sK1) | ~spl5_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    spl5_15 | ~spl5_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f128,f116,f146])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    v5_relat_1(sK3,sK1) | ~spl5_10),
% 0.20/0.55    inference(resolution,[],[f118,f57])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ~spl5_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f39,f135])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & (v2_funct_2(X4,X2) & v2_funct_2(X3,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 0.20/0.55    inference(negated_conjecture,[],[f14])).
% 0.20/0.55  fof(f14,conjecture,(
% 0.20/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_funct_2)).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    spl5_12 | ~spl5_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f121,f111,f130])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    v5_relat_1(sK4,sK2) | ~spl5_9),
% 0.20/0.55    inference(resolution,[],[f113,f57])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    spl5_11 | ~spl5_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f120,f111,f123])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    v4_relat_1(sK4,sK1) | ~spl5_9),
% 0.20/0.55    inference(resolution,[],[f113,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    spl5_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f42,f116])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl5_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f36,f111])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    spl5_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f38,f88])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    v2_funct_2(sK4,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    spl5_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f37,f83])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    v2_funct_2(sK3,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    spl5_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f40,f68])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    spl5_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f63])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    v1_funct_1(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (21959)------------------------------
% 0.20/0.55  % (21959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21959)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (21959)Memory used [KB]: 11001
% 0.20/0.55  % (21959)Time elapsed: 0.109 s
% 0.20/0.55  % (21959)------------------------------
% 0.20/0.55  % (21959)------------------------------
% 0.20/0.55  % (21954)Success in time 0.19 s
%------------------------------------------------------------------------------
