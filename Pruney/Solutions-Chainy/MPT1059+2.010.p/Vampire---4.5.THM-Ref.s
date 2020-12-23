%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 235 expanded)
%              Number of leaves         :   38 (  99 expanded)
%              Depth                    :    8
%              Number of atoms          :  491 ( 825 expanded)
%              Number of equality atoms :   75 ( 122 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f84,f88,f92,f96,f116,f120,f125,f129,f143,f155,f177,f185,f199,f205,f213,f218,f222,f231,f253,f256,f259,f265])).

fof(f265,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_16
    | spl5_41 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_16
    | spl5_41 ),
    inference(subsumption_resolution,[],[f263,f71])).

fof(f71,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f263,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | spl5_3
    | ~ spl5_16
    | spl5_41 ),
    inference(subsumption_resolution,[],[f261,f67])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f261,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ spl5_16
    | spl5_41 ),
    inference(resolution,[],[f252,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f252,plain,
    ( ~ r2_hidden(sK3,sK0)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl5_41
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f259,plain,
    ( ~ spl5_6
    | ~ spl5_20
    | spl5_40 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_20
    | spl5_40 ),
    inference(unit_resulting_resolution,[],[f79,f249,f142])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f249,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl5_40 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_40
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f256,plain,
    ( ~ spl5_6
    | ~ spl5_17
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_17
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f79,f246,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f246,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl5_39
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f253,plain,
    ( ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_1
    | ~ spl5_27
    | ~ spl5_34
    | spl5_36 ),
    inference(avatar_split_clause,[],[f239,f229,f216,f175,f58,f251,f248,f245])).

fof(f58,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f175,plain,
    ( spl5_27
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f216,plain,
    ( spl5_34
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f229,plain,
    ( spl5_36
  <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f239,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_27
    | ~ spl5_34
    | spl5_36 ),
    inference(forward_demodulation,[],[f238,f217])).

fof(f217,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f216])).

fof(f238,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_27
    | spl5_36 ),
    inference(subsumption_resolution,[],[f237,f59])).

fof(f59,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f237,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_27
    | spl5_36 ),
    inference(trivial_inequality_removal,[],[f236])).

fof(f236,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_27
    | spl5_36 ),
    inference(superposition,[],[f230,f176])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f175])).

fof(f230,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl5_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( ~ spl5_36
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f227,f220,f86,f78,f74,f70,f66,f229])).

fof(f74,plain,
    ( spl5_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( spl5_8
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f220,plain,
    ( spl5_35
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f227,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f226,f67])).

fof(f226,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | v1_xboole_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f225,f71])).

fof(f225,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f224,f79])).

fof(f224,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0)
    | ~ spl5_5
    | spl5_8
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f223,f75])).

fof(f75,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f223,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0)
    | spl5_8
    | ~ spl5_35 ),
    inference(superposition,[],[f87,f221])).

fof(f221,plain,
    ( ! [X2,X0,X1] :
        ( k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f220])).

fof(f87,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f222,plain,
    ( spl5_35
    | ~ spl5_1
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f214,f211,f58,f220])).

fof(f211,plain,
    ( spl5_33
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) )
    | ~ spl5_1
    | ~ spl5_33 ),
    inference(resolution,[],[f212,f59])).

fof(f212,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f211])).

fof(f218,plain,
    ( spl5_34
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f209,f194,f153,f78,f216])).

fof(f153,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f194,plain,
    ( spl5_31
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f209,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f207,f79])).

fof(f207,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_22
    | ~ spl5_31 ),
    inference(superposition,[],[f195,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f195,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f194])).

fof(f213,plain,(
    spl5_33 ),
    inference(avatar_split_clause,[],[f50,f211])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f205,plain,
    ( spl5_2
    | ~ spl5_14
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl5_2
    | ~ spl5_14
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f203,f112])).

fof(f112,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f203,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_32 ),
    inference(backward_demodulation,[],[f63,f198])).

% (28530)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f198,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl5_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f63,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f199,plain,
    ( spl5_31
    | spl5_32
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f192,f183,f78,f74,f197,f194])).

fof(f183,plain,
    ( spl5_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f190,f75])).

fof(f190,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(resolution,[],[f184,f79])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,(
    spl5_29 ),
    inference(avatar_split_clause,[],[f49,f183])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f177,plain,(
    spl5_27 ),
    inference(avatar_split_clause,[],[f39,f175])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f155,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f41,f153])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f143,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f43,f141])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f129,plain,
    ( ~ spl5_7
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f83,f115])).

fof(f115,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_15
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f83,plain,
    ( v1_xboole_0(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_7
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f125,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f40,f123])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f120,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f37,f118])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f116,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f105,f94,f90,f114,f111])).

fof(f90,plain,
    ( spl5_9
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f94,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k1_xboole_0) )
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(superposition,[],[f95,f91])).

fof(f91,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
        | v1_xboole_0(X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f92,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f33,f90])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f88,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f27,f86])).

fof(f27,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f84,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f51,f82])).

fof(f51,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f80,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (28528)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.46  % (28529)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.46  % (28528)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (28522)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (28532)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f266,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f84,f88,f92,f96,f116,f120,f125,f129,f143,f155,f177,f185,f199,f205,f213,f218,f222,f231,f253,f256,f259,f265])).
% 0.19/0.47  fof(f265,plain,(
% 0.19/0.47    spl5_3 | ~spl5_4 | ~spl5_16 | spl5_41),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f264])).
% 0.19/0.47  fof(f264,plain,(
% 0.19/0.47    $false | (spl5_3 | ~spl5_4 | ~spl5_16 | spl5_41)),
% 0.19/0.47    inference(subsumption_resolution,[],[f263,f71])).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    m1_subset_1(sK3,sK0) | ~spl5_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f70])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    spl5_4 <=> m1_subset_1(sK3,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.47  fof(f263,plain,(
% 0.19/0.47    ~m1_subset_1(sK3,sK0) | (spl5_3 | ~spl5_16 | spl5_41)),
% 0.19/0.47    inference(subsumption_resolution,[],[f261,f67])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    ~v1_xboole_0(sK0) | spl5_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f66])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    spl5_3 <=> v1_xboole_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.47  fof(f261,plain,(
% 0.19/0.47    v1_xboole_0(sK0) | ~m1_subset_1(sK3,sK0) | (~spl5_16 | spl5_41)),
% 0.19/0.47    inference(resolution,[],[f252,f119])).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | ~spl5_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f118])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    spl5_16 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.47  fof(f252,plain,(
% 0.19/0.47    ~r2_hidden(sK3,sK0) | spl5_41),
% 0.19/0.47    inference(avatar_component_clause,[],[f251])).
% 0.19/0.47  fof(f251,plain,(
% 0.19/0.47    spl5_41 <=> r2_hidden(sK3,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.19/0.47  fof(f259,plain,(
% 0.19/0.47    ~spl5_6 | ~spl5_20 | spl5_40),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f257])).
% 0.19/0.47  fof(f257,plain,(
% 0.19/0.47    $false | (~spl5_6 | ~spl5_20 | spl5_40)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f79,f249,f142])).
% 0.19/0.47  fof(f142,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_20),
% 0.19/0.47    inference(avatar_component_clause,[],[f141])).
% 0.19/0.47  fof(f141,plain,(
% 0.19/0.47    spl5_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.19/0.47  fof(f249,plain,(
% 0.19/0.47    ~v5_relat_1(sK2,sK1) | spl5_40),
% 0.19/0.47    inference(avatar_component_clause,[],[f248])).
% 0.19/0.47  fof(f248,plain,(
% 0.19/0.47    spl5_40 <=> v5_relat_1(sK2,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.19/0.47  fof(f79,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f78])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    spl5_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.47  fof(f256,plain,(
% 0.19/0.47    ~spl5_6 | ~spl5_17 | spl5_39),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f254])).
% 0.19/0.47  fof(f254,plain,(
% 0.19/0.47    $false | (~spl5_6 | ~spl5_17 | spl5_39)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f79,f246,f124])).
% 0.19/0.47  fof(f124,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_17),
% 0.19/0.47    inference(avatar_component_clause,[],[f123])).
% 0.19/0.47  fof(f123,plain,(
% 0.19/0.47    spl5_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.19/0.47  fof(f246,plain,(
% 0.19/0.47    ~v1_relat_1(sK2) | spl5_39),
% 0.19/0.47    inference(avatar_component_clause,[],[f245])).
% 0.19/0.47  fof(f245,plain,(
% 0.19/0.47    spl5_39 <=> v1_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.19/0.47  fof(f253,plain,(
% 0.19/0.47    ~spl5_39 | ~spl5_40 | ~spl5_41 | ~spl5_1 | ~spl5_27 | ~spl5_34 | spl5_36),
% 0.19/0.47    inference(avatar_split_clause,[],[f239,f229,f216,f175,f58,f251,f248,f245])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    spl5_1 <=> v1_funct_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.47  fof(f175,plain,(
% 0.19/0.47    spl5_27 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.19/0.47  fof(f216,plain,(
% 0.19/0.47    spl5_34 <=> sK0 = k1_relat_1(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.19/0.47  fof(f229,plain,(
% 0.19/0.47    spl5_36 <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.19/0.47  fof(f239,plain,(
% 0.19/0.47    ~r2_hidden(sK3,sK0) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_27 | ~spl5_34 | spl5_36)),
% 0.19/0.47    inference(forward_demodulation,[],[f238,f217])).
% 0.19/0.47  fof(f217,plain,(
% 0.19/0.47    sK0 = k1_relat_1(sK2) | ~spl5_34),
% 0.19/0.47    inference(avatar_component_clause,[],[f216])).
% 0.19/0.47  fof(f238,plain,(
% 0.19/0.47    ~v5_relat_1(sK2,sK1) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_27 | spl5_36)),
% 0.19/0.47    inference(subsumption_resolution,[],[f237,f59])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    v1_funct_1(sK2) | ~spl5_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f58])).
% 0.19/0.47  fof(f237,plain,(
% 0.19/0.47    ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_27 | spl5_36)),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f236])).
% 0.19/0.47  fof(f236,plain,(
% 0.19/0.47    k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3) | ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_27 | spl5_36)),
% 0.19/0.47    inference(superposition,[],[f230,f176])).
% 0.19/0.47  fof(f176,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl5_27),
% 0.19/0.47    inference(avatar_component_clause,[],[f175])).
% 0.19/0.47  fof(f230,plain,(
% 0.19/0.47    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | spl5_36),
% 0.19/0.47    inference(avatar_component_clause,[],[f229])).
% 0.19/0.47  fof(f231,plain,(
% 0.19/0.47    ~spl5_36 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_35),
% 0.19/0.47    inference(avatar_split_clause,[],[f227,f220,f86,f78,f74,f70,f66,f229])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    spl5_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    spl5_8 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.47  fof(f220,plain,(
% 0.19/0.47    spl5_35 <=> ! [X1,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.19/0.47  fof(f227,plain,(
% 0.19/0.47    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_35)),
% 0.19/0.47    inference(subsumption_resolution,[],[f226,f67])).
% 0.19/0.47  fof(f226,plain,(
% 0.19/0.47    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | v1_xboole_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_35)),
% 0.19/0.47    inference(subsumption_resolution,[],[f225,f71])).
% 0.19/0.47  fof(f225,plain,(
% 0.19/0.47    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | ~m1_subset_1(sK3,sK0) | v1_xboole_0(sK0) | (~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_35)),
% 0.19/0.47    inference(subsumption_resolution,[],[f224,f79])).
% 0.19/0.47  fof(f224,plain,(
% 0.19/0.47    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,sK0) | v1_xboole_0(sK0) | (~spl5_5 | spl5_8 | ~spl5_35)),
% 0.19/0.47    inference(subsumption_resolution,[],[f223,f75])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    v1_funct_2(sK2,sK0,sK1) | ~spl5_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f74])).
% 0.19/0.47  fof(f223,plain,(
% 0.19/0.47    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,sK0) | v1_xboole_0(sK0) | (spl5_8 | ~spl5_35)),
% 0.19/0.47    inference(superposition,[],[f87,f221])).
% 0.19/0.47  fof(f221,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) ) | ~spl5_35),
% 0.19/0.47    inference(avatar_component_clause,[],[f220])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) | spl5_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f86])).
% 0.19/0.47  fof(f222,plain,(
% 0.19/0.47    spl5_35 | ~spl5_1 | ~spl5_33),
% 0.19/0.47    inference(avatar_split_clause,[],[f214,f211,f58,f220])).
% 0.19/0.47  fof(f211,plain,(
% 0.19/0.47    spl5_33 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.19/0.47  fof(f214,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2)) ) | (~spl5_1 | ~spl5_33)),
% 0.19/0.47    inference(resolution,[],[f212,f59])).
% 0.19/0.47  fof(f212,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) ) | ~spl5_33),
% 0.19/0.47    inference(avatar_component_clause,[],[f211])).
% 0.19/0.47  fof(f218,plain,(
% 0.19/0.47    spl5_34 | ~spl5_6 | ~spl5_22 | ~spl5_31),
% 0.19/0.47    inference(avatar_split_clause,[],[f209,f194,f153,f78,f216])).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    spl5_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.19/0.47  fof(f194,plain,(
% 0.19/0.47    spl5_31 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.19/0.47  fof(f209,plain,(
% 0.19/0.47    sK0 = k1_relat_1(sK2) | (~spl5_6 | ~spl5_22 | ~spl5_31)),
% 0.19/0.47    inference(subsumption_resolution,[],[f207,f79])).
% 0.19/0.47  fof(f207,plain,(
% 0.19/0.47    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_22 | ~spl5_31)),
% 0.19/0.47    inference(superposition,[],[f195,f154])).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_22),
% 0.19/0.47    inference(avatar_component_clause,[],[f153])).
% 0.19/0.47  fof(f195,plain,(
% 0.19/0.47    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_31),
% 0.19/0.47    inference(avatar_component_clause,[],[f194])).
% 0.19/0.47  fof(f213,plain,(
% 0.19/0.47    spl5_33),
% 0.19/0.47    inference(avatar_split_clause,[],[f50,f211])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.19/0.47    inference(flattening,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.19/0.47  fof(f205,plain,(
% 0.19/0.47    spl5_2 | ~spl5_14 | ~spl5_32),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f204])).
% 0.19/0.47  fof(f204,plain,(
% 0.19/0.47    $false | (spl5_2 | ~spl5_14 | ~spl5_32)),
% 0.19/0.47    inference(subsumption_resolution,[],[f203,f112])).
% 0.19/0.47  fof(f112,plain,(
% 0.19/0.47    v1_xboole_0(k1_xboole_0) | ~spl5_14),
% 0.19/0.47    inference(avatar_component_clause,[],[f111])).
% 0.19/0.47  fof(f111,plain,(
% 0.19/0.47    spl5_14 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.19/0.47  fof(f203,plain,(
% 0.19/0.47    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_32)),
% 0.19/0.47    inference(backward_demodulation,[],[f63,f198])).
% 0.19/0.47  % (28530)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.47  fof(f198,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | ~spl5_32),
% 0.19/0.47    inference(avatar_component_clause,[],[f197])).
% 0.19/0.47  fof(f197,plain,(
% 0.19/0.47    spl5_32 <=> k1_xboole_0 = sK1),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ~v1_xboole_0(sK1) | spl5_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f62])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    spl5_2 <=> v1_xboole_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.47  fof(f199,plain,(
% 0.19/0.47    spl5_31 | spl5_32 | ~spl5_5 | ~spl5_6 | ~spl5_29),
% 0.19/0.47    inference(avatar_split_clause,[],[f192,f183,f78,f74,f197,f194])).
% 0.19/0.47  fof(f183,plain,(
% 0.19/0.47    spl5_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.19/0.47  fof(f192,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_5 | ~spl5_6 | ~spl5_29)),
% 0.19/0.47    inference(subsumption_resolution,[],[f190,f75])).
% 0.19/0.47  fof(f190,plain,(
% 0.19/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | (~spl5_6 | ~spl5_29)),
% 0.19/0.47    inference(resolution,[],[f184,f79])).
% 0.19/0.47  fof(f184,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl5_29),
% 0.19/0.47    inference(avatar_component_clause,[],[f183])).
% 0.19/0.47  fof(f185,plain,(
% 0.19/0.47    spl5_29),
% 0.19/0.47    inference(avatar_split_clause,[],[f49,f183])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.47  fof(f177,plain,(
% 0.19/0.47    spl5_27),
% 0.19/0.47    inference(avatar_split_clause,[],[f39,f175])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    spl5_22),
% 0.19/0.47    inference(avatar_split_clause,[],[f41,f153])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.47  fof(f143,plain,(
% 0.19/0.47    spl5_20),
% 0.19/0.47    inference(avatar_split_clause,[],[f43,f141])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    ~spl5_7 | ~spl5_15),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f126])).
% 0.19/0.47  fof(f126,plain,(
% 0.19/0.47    $false | (~spl5_7 | ~spl5_15)),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f83,f115])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl5_15),
% 0.19/0.47    inference(avatar_component_clause,[],[f114])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    spl5_15 <=> ! [X0] : ~v1_xboole_0(X0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.19/0.47  fof(f83,plain,(
% 0.19/0.47    v1_xboole_0(sK4) | ~spl5_7),
% 0.19/0.47    inference(avatar_component_clause,[],[f82])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    spl5_7 <=> v1_xboole_0(sK4)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.47  fof(f125,plain,(
% 0.19/0.47    spl5_17),
% 0.19/0.47    inference(avatar_split_clause,[],[f40,f123])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    spl5_16),
% 0.19/0.47    inference(avatar_split_clause,[],[f37,f118])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    spl5_14 | spl5_15 | ~spl5_9 | ~spl5_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f105,f94,f90,f114,f111])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    spl5_9 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.47  fof(f94,plain,(
% 0.19/0.47    spl5_10 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_xboole_0)) ) | (~spl5_9 | ~spl5_10)),
% 0.19/0.47    inference(superposition,[],[f95,f91])).
% 0.19/0.47  fof(f91,plain,(
% 0.19/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f90])).
% 0.19/0.47  fof(f95,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) ) | ~spl5_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f94])).
% 0.19/0.47  fof(f96,plain,(
% 0.19/0.47    spl5_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f38,f94])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_xboole_0(X1,X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    spl5_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f33,f90])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    ~spl5_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f27,f86])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.47    inference(flattening,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,negated_conjecture,(
% 0.19/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.19/0.47    inference(negated_conjecture,[],[f11])).
% 0.19/0.47  fof(f11,conjecture,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    spl5_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f51,f82])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    v1_xboole_0(sK4)),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ? [X0] : v1_xboole_0(X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    spl5_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f30,f78])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    spl5_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f29,f74])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    spl5_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f26,f70])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    m1_subset_1(sK3,sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    ~spl5_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f32,f66])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ~v1_xboole_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ~spl5_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f31,f62])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ~v1_xboole_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    spl5_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f28,f58])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (28528)------------------------------
% 0.19/0.47  % (28528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (28528)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (28528)Memory used [KB]: 10746
% 0.19/0.47  % (28528)Time elapsed: 0.057 s
% 0.19/0.47  % (28528)------------------------------
% 0.19/0.47  % (28528)------------------------------
% 0.19/0.47  % (28518)Success in time 0.123 s
%------------------------------------------------------------------------------
