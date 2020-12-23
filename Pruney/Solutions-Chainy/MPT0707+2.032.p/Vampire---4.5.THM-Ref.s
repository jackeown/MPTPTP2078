%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 178 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :    6
%              Number of atoms          :  312 ( 465 expanded)
%              Number of equality atoms :   58 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f75,f79,f87,f92,f96,f104,f110,f114,f127,f131,f137,f153,f157,f165,f176,f182,f190,f203])).

fof(f203,plain,
    ( ~ spl3_5
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(unit_resulting_resolution,[],[f62,f189])).

fof(f189,plain,
    ( ! [X0] : ~ v4_relat_1(k6_relat_1(sK1),X0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl3_30
  <=> ! [X0] : ~ v4_relat_1(k6_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f62,plain,
    ( ! [X0] : v4_relat_1(k6_relat_1(X0),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_5
  <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f190,plain,
    ( spl3_30
    | spl3_2
    | ~ spl3_24
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f186,f180,f151,f49,f188])).

fof(f49,plain,
    ( spl3_2
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f151,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( k9_relat_1(k6_relat_1(X0),X1) = X0
        | ~ v4_relat_1(k6_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f180,plain,
    ( spl3_29
  <=> ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f186,plain,
    ( ! [X0] : ~ v4_relat_1(k6_relat_1(sK1),X0)
    | spl3_2
    | ~ spl3_24
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f183,f50])).

fof(f50,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f183,plain,
    ( ! [X0] :
        ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
        | ~ v4_relat_1(k6_relat_1(sK1),X0) )
    | ~ spl3_24
    | ~ spl3_29 ),
    inference(superposition,[],[f181,f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) = X0
        | ~ v4_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f181,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl3_29
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f177,f174,f125,f180])).

fof(f125,plain,
    ( spl3_20
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f174,plain,
    ( spl3_28
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f177,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(resolution,[],[f175,f126])).

fof(f126,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f125])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f172,f163,f108,f73,f57,f174])).

fof(f57,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( spl3_8
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f163,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) )
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f171,f74])).

fof(f74,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
        | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) )
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f170,f58])).

fof(f58,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
        | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(superposition,[],[f164,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f164,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f161,f155,f57,f163])).

fof(f155,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f161,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(resolution,[],[f156,f58])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl3_25
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f138,f129,f57,f155])).

fof(f129,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) )
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(resolution,[],[f130,f58])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f129])).

fof(f153,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f141,f135,f90,f73,f57,f151])).

fof(f90,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f135,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ v4_relat_1(k6_relat_1(X0),X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) = X0
        | ~ v4_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f140,f74])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X1)
        | ~ v4_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v4_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(superposition,[],[f91,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ v4_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f135])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f137,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f105,f94,f57,f135])).

fof(f94,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(k6_relat_1(X0),X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(resolution,[],[f95,f58])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f131,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f34,f129])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f127,plain,
    ( spl3_20
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f115,f112,f77,f125])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f112,plain,
    ( spl3_17
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f115,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(resolution,[],[f113,f78])).

fof(f78,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f113,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f106,f102,f45,f112])).

fof(f45,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f106,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(resolution,[],[f103,f46])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f110,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f33,f108])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f104,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f88,f85,f53,f102])).

fof(f53,plain,
    ( spl3_3
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f86,f54])).

fof(f54,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f96,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f92,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f87,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f75,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f63,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f51,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f47,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.42  % (1724)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.43  % (1731)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.44  % (1731)Refutation not found, incomplete strategy% (1731)------------------------------
% 0.20/0.44  % (1731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (1731)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (1731)Memory used [KB]: 6012
% 0.20/0.44  % (1731)Time elapsed: 0.003 s
% 0.20/0.44  % (1731)------------------------------
% 0.20/0.44  % (1731)------------------------------
% 0.20/0.46  % (1728)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (1728)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f205,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f75,f79,f87,f92,f96,f104,f110,f114,f127,f131,f137,f153,f157,f165,f176,f182,f190,f203])).
% 0.20/0.46  fof(f203,plain,(
% 0.20/0.46    ~spl3_5 | ~spl3_30),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.46  fof(f198,plain,(
% 0.20/0.46    $false | (~spl3_5 | ~spl3_30)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f62,f189])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    ( ! [X0] : (~v4_relat_1(k6_relat_1(sK1),X0)) ) | ~spl3_30),
% 0.20/0.46    inference(avatar_component_clause,[],[f188])).
% 0.20/0.46  fof(f188,plain,(
% 0.20/0.46    spl3_30 <=> ! [X0] : ~v4_relat_1(k6_relat_1(sK1),X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) ) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_5 <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f190,plain,(
% 0.20/0.46    spl3_30 | spl3_2 | ~spl3_24 | ~spl3_29),
% 0.20/0.46    inference(avatar_split_clause,[],[f186,f180,f151,f49,f188])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl3_2 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    spl3_24 <=> ! [X1,X0] : (k9_relat_1(k6_relat_1(X0),X1) = X0 | ~v4_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.46  fof(f180,plain,(
% 0.20/0.46    spl3_29 <=> ! [X0] : k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    ( ! [X0] : (~v4_relat_1(k6_relat_1(sK1),X0)) ) | (spl3_2 | ~spl3_24 | ~spl3_29)),
% 0.20/0.46    inference(subsumption_resolution,[],[f183,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f183,plain,(
% 0.20/0.46    ( ! [X0] : (sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | ~v4_relat_1(k6_relat_1(sK1),X0)) ) | (~spl3_24 | ~spl3_29)),
% 0.20/0.46    inference(superposition,[],[f181,f152])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X0 | ~v4_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f151])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    ( ! [X0] : (k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))) ) | ~spl3_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f180])).
% 0.20/0.46  fof(f182,plain,(
% 0.20/0.46    spl3_29 | ~spl3_20 | ~spl3_28),
% 0.20/0.46    inference(avatar_split_clause,[],[f177,f174,f125,f180])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    spl3_20 <=> r1_tarski(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    spl3_28 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.46  fof(f177,plain,(
% 0.20/0.46    ( ! [X0] : (k9_relat_1(k6_relat_1(sK1),X0) = k9_relat_1(k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK1),X0))) ) | (~spl3_20 | ~spl3_28)),
% 0.20/0.46    inference(resolution,[],[f175,f126])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    r1_tarski(sK1,sK0) | ~spl3_20),
% 0.20/0.46    inference(avatar_component_clause,[],[f125])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | ~spl3_28),
% 0.20/0.46    inference(avatar_component_clause,[],[f174])).
% 0.20/0.46  fof(f176,plain,(
% 0.20/0.46    spl3_28 | ~spl3_4 | ~spl3_8 | ~spl3_16 | ~spl3_26),
% 0.20/0.46    inference(avatar_split_clause,[],[f172,f163,f108,f73,f57,f174])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    spl3_8 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    spl3_16 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    spl3_26 <=> ! [X1,X0,X2] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | (~spl3_4 | ~spl3_8 | ~spl3_16 | ~spl3_26)),
% 0.20/0.46    inference(forward_demodulation,[],[f171,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f73])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) ) | (~spl3_4 | ~spl3_16 | ~spl3_26)),
% 0.20/0.46    inference(subsumption_resolution,[],[f170,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f57])).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X0),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl3_16 | ~spl3_26)),
% 0.20/0.46    inference(superposition,[],[f164,f109])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f108])).
% 0.20/0.46  fof(f164,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | ~spl3_26),
% 0.20/0.46    inference(avatar_component_clause,[],[f163])).
% 0.20/0.46  fof(f165,plain,(
% 0.20/0.46    spl3_26 | ~spl3_4 | ~spl3_25),
% 0.20/0.46    inference(avatar_split_clause,[],[f161,f155,f57,f163])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    spl3_25 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | (~spl3_4 | ~spl3_25)),
% 0.20/0.46    inference(resolution,[],[f156,f58])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2))) ) | ~spl3_25),
% 0.20/0.46    inference(avatar_component_clause,[],[f155])).
% 0.20/0.46  fof(f157,plain,(
% 0.20/0.46    spl3_25 | ~spl3_4 | ~spl3_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f138,f129,f57,f155])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    spl3_21 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2))) ) | (~spl3_4 | ~spl3_21)),
% 0.20/0.46    inference(resolution,[],[f130,f58])).
% 0.20/0.46  fof(f130,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl3_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f129])).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    spl3_24 | ~spl3_4 | ~spl3_8 | ~spl3_12 | ~spl3_22),
% 0.20/0.46    inference(avatar_split_clause,[],[f141,f135,f90,f73,f57,f151])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl3_12 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    spl3_22 <=> ! [X1,X0] : (~v4_relat_1(k6_relat_1(X0),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X0 | ~v4_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_4 | ~spl3_8 | ~spl3_12 | ~spl3_22)),
% 0.20/0.46    inference(forward_demodulation,[],[f140,f74])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X1) | ~v4_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_4 | ~spl3_12 | ~spl3_22)),
% 0.20/0.46    inference(subsumption_resolution,[],[f139,f58])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v4_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_12 | ~spl3_22)),
% 0.20/0.46    inference(superposition,[],[f91,f136])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v4_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_22),
% 0.20/0.46    inference(avatar_component_clause,[],[f135])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f90])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl3_22 | ~spl3_4 | ~spl3_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f105,f94,f57,f135])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_4 | ~spl3_13)),
% 0.20/0.46    inference(resolution,[],[f95,f58])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) ) | ~spl3_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f94])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    spl3_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f34,f129])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    spl3_20 | ~spl3_9 | ~spl3_17),
% 0.20/0.46    inference(avatar_split_clause,[],[f115,f112,f77,f125])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    spl3_9 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    spl3_17 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    r1_tarski(sK1,sK0) | (~spl3_9 | ~spl3_17)),
% 0.20/0.46    inference(resolution,[],[f113,f78])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl3_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f77])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_17),
% 0.20/0.46    inference(avatar_component_clause,[],[f112])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    spl3_17 | ~spl3_1 | ~spl3_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f106,f102,f45,f112])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_15)),
% 0.20/0.46    inference(resolution,[],[f103,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1))) ) | ~spl3_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f102])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl3_16),
% 0.20/0.46    inference(avatar_split_clause,[],[f33,f108])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl3_15 | ~spl3_3 | ~spl3_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f88,f85,f53,f102])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl3_3 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    spl3_11 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1))) ) | (~spl3_3 | ~spl3_11)),
% 0.20/0.46    inference(resolution,[],[f86,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl3_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f85])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    spl3_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f37,f94])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl3_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f90])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl3_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f36,f85])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    spl3_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f42,f77])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(equality_resolution,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    spl3_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f31,f73])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f61])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f57])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f53])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f49])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.46    inference(negated_conjecture,[],[f11])).
% 0.20/0.46  fof(f11,conjecture,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f45])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (1728)------------------------------
% 0.20/0.46  % (1728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (1728)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (1728)Memory used [KB]: 10746
% 0.20/0.46  % (1728)Time elapsed: 0.054 s
% 0.20/0.46  % (1728)------------------------------
% 0.20/0.46  % (1728)------------------------------
% 0.20/0.47  % (1714)Success in time 0.113 s
%------------------------------------------------------------------------------
