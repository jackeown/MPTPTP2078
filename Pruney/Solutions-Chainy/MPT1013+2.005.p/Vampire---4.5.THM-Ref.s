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
% DateTime   : Thu Dec  3 13:05:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 238 expanded)
%              Number of leaves         :   38 ( 107 expanded)
%              Depth                    :    6
%              Number of atoms          :  422 ( 696 expanded)
%              Number of equality atoms :   67 ( 145 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f82,f86,f91,f95,f99,f104,f112,f125,f134,f138,f142,f146,f150,f192,f201,f212,f226,f229,f232,f237,f240])).

fof(f240,plain,
    ( ~ spl4_4
    | ~ spl4_22
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_22
    | spl4_37 ),
    inference(unit_resulting_resolution,[],[f61,f236,f145])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f236,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_37
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f237,plain,
    ( ~ spl4_37
    | ~ spl4_16
    | spl4_36 ),
    inference(avatar_split_clause,[],[f233,f224,f110,f235])).

fof(f110,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f224,plain,
    ( spl4_36
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f233,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_16
    | spl4_36 ),
    inference(resolution,[],[f225,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f225,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f224])).

fof(f232,plain,
    ( ~ spl4_1
    | ~ spl4_10
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_10
    | spl4_35 ),
    inference(unit_resulting_resolution,[],[f49,f222,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f222,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_35
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f229,plain,
    ( ~ spl4_4
    | ~ spl4_10
    | spl4_34 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_10
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f61,f219,f85])).

fof(f219,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_34
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f226,plain,
    ( ~ spl4_34
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | spl4_33 ),
    inference(avatar_split_clause,[],[f216,f210,f136,f132,f123,f224,f221,f218])).

fof(f123,plain,
    ( spl4_18
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f132,plain,
    ( spl4_19
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f136,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f210,plain,
    ( spl4_33
  <=> sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f216,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | spl4_33 ),
    inference(forward_demodulation,[],[f215,f124])).

fof(f124,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f215,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl4_19
    | ~ spl4_20
    | spl4_33 ),
    inference(subsumption_resolution,[],[f214,f133])).

fof(f133,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f132])).

% (16094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f214,plain,
    ( sK0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl4_20
    | spl4_33 ),
    inference(superposition,[],[f211,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f211,plain,
    ( sK0 != k2_relat_1(k5_relat_1(sK2,sK1))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( ~ spl4_33
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_21
    | spl4_31 ),
    inference(avatar_split_clause,[],[f204,f199,f140,f60,f48,f210])).

fof(f140,plain,
    ( spl4_21
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f199,plain,
    ( spl4_31
  <=> sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f204,plain,
    ( sK0 != k2_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_21
    | spl4_31 ),
    inference(subsumption_resolution,[],[f203,f49])).

fof(f203,plain,
    ( sK0 != k2_relat_1(k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4
    | ~ spl4_21
    | spl4_31 ),
    inference(subsumption_resolution,[],[f202,f61])).

fof(f202,plain,
    ( sK0 != k2_relat_1(k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_21
    | spl4_31 ),
    inference(superposition,[],[f200,f141])).

fof(f141,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f140])).

fof(f200,plain,
    ( sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( ~ spl4_31
    | ~ spl4_1
    | ~ spl4_4
    | spl4_6
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f197,f190,f68,f60,f48,f199])).

fof(f68,plain,
    ( spl4_6
  <=> sK0 = k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f190,plain,
    ( spl4_30
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k2_relset_1(X4,X2,k4_relset_1(X4,X5,X1,X2,X3,X0)) = k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f197,plain,
    ( sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | ~ spl4_1
    | ~ spl4_4
    | spl4_6
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f196,f61])).

fof(f196,plain,
    ( sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | spl4_6
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f194,f49])).

fof(f194,plain,
    ( sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_6
    | ~ spl4_30 ),
    inference(superposition,[],[f69,f191])).

fof(f191,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k2_relset_1(X4,X2,k4_relset_1(X4,X5,X1,X2,X3,X0)) = k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f190])).

fof(f69,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f192,plain,
    ( spl4_30
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f155,f148,f97,f190])).

fof(f97,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f148,plain,
    ( spl4_23
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f155,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k2_relset_1(X4,X2,k4_relset_1(X4,X5,X1,X2,X3,X0)) = k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0)) )
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(resolution,[],[f149,f98])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f149,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f44,f148])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f146,plain,
    ( spl4_22
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f128,f102,f89,f144])).

fof(f89,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f102,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(superposition,[],[f103,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f142,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f43,f140])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f138,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f33,f136])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f134,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f121,f97,f60,f52,f132])).

fof(f52,plain,
    ( spl4_2
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f121,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f119,f53])).

fof(f53,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f119,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(resolution,[],[f98,f61])).

fof(f125,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f120,f97,f56,f48,f123])).

fof(f56,plain,
    ( spl4_3
  <=> sK0 = k2_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f118,f57])).

fof(f57,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f118,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(resolution,[],[f98,f49])).

fof(f112,plain,
    ( spl4_16
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f100,f93,f72,f110])).

fof(f72,plain,
    ( spl4_7
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f93,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f94,f73])).

fof(f73,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f104,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f42,f102])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f99,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f41,f97])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f95,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f87,f80,f64,f93])).

fof(f64,plain,
    ( spl4_5
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f80,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f81,f65])).

fof(f65,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f91,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f86,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
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

fof(f82,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f74,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f70,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f62,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (16086)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (16080)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (16083)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (16088)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (16080)Refutation not found, incomplete strategy% (16080)------------------------------
% 0.21/0.47  % (16080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (16080)Memory used [KB]: 10618
% 0.21/0.47  % (16080)Time elapsed: 0.063 s
% 0.21/0.47  % (16080)------------------------------
% 0.21/0.47  % (16080)------------------------------
% 0.21/0.47  % (16095)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (16081)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (16088)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f74,f82,f86,f91,f95,f99,f104,f112,f125,f134,f138,f142,f146,f150,f192,f201,f212,f226,f229,f232,f237,f240])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~spl4_4 | ~spl4_22 | spl4_37),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    $false | (~spl4_4 | ~spl4_22 | spl4_37)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f61,f236,f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl4_22 <=> ! [X1,X0,X2] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | spl4_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f235])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    spl4_37 <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ~spl4_37 | ~spl4_16 | spl4_36),
% 0.21/0.48    inference(avatar_split_clause,[],[f233,f224,f110,f235])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl4_16 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    spl4_36 <=> r1_tarski(k1_relat_1(sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | (~spl4_16 | spl4_36)),
% 0.21/0.48    inference(resolution,[],[f225,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK1),sK0) | spl4_36),
% 0.21/0.48    inference(avatar_component_clause,[],[f224])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_10 | spl4_35),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_10 | spl4_35)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f222,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl4_10 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl4_35),
% 0.21/0.48    inference(avatar_component_clause,[],[f221])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl4_35 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ~spl4_4 | ~spl4_10 | spl4_34),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    $false | (~spl4_4 | ~spl4_10 | spl4_34)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f61,f219,f85])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl4_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl4_34 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~spl4_34 | ~spl4_35 | ~spl4_36 | ~spl4_18 | ~spl4_19 | ~spl4_20 | spl4_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f216,f210,f136,f132,f123,f224,f221,f218])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl4_18 <=> sK0 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl4_19 <=> sK0 = k2_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl4_20 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    spl4_33 <=> sK0 = k2_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | (~spl4_18 | ~spl4_19 | ~spl4_20 | spl4_33)),
% 0.21/0.48    inference(forward_demodulation,[],[f215,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK2) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f123])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK1) | (~spl4_19 | ~spl4_20 | spl4_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f214,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK1) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  % (16094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    sK0 != k2_relat_1(sK1) | ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK1) | (~spl4_20 | spl4_33)),
% 0.21/0.48    inference(superposition,[],[f211,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X0)) ) | ~spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) | spl4_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f210])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ~spl4_33 | ~spl4_1 | ~spl4_4 | ~spl4_21 | spl4_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f204,f199,f140,f60,f48,f210])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl4_21 <=> ! [X1,X3,X5,X0,X2,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl4_31 <=> sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) | (~spl4_1 | ~spl4_4 | ~spl4_21 | spl4_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f49])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_4 | ~spl4_21 | spl4_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f61])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_21 | spl4_31)),
% 0.21/0.48    inference(superposition,[],[f200,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) | spl4_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f199])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ~spl4_31 | ~spl4_1 | ~spl4_4 | spl4_6 | ~spl4_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f197,f190,f68,f60,f48,f199])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_6 <=> sK0 = k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl4_30 <=> ! [X1,X3,X5,X0,X2,X4] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k2_relset_1(X4,X2,k4_relset_1(X4,X5,X1,X2,X3,X0)) = k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) | (~spl4_1 | ~spl4_4 | spl4_6 | ~spl4_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f196,f61])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | spl4_6 | ~spl4_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f194,f49])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl4_6 | ~spl4_30)),
% 0.21/0.48    inference(superposition,[],[f69,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_relset_1(X4,X2,k4_relset_1(X4,X5,X1,X2,X3,X0)) = k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f190])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) | spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    spl4_30 | ~spl4_13 | ~spl4_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f148,f97,f190])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl4_13 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl4_23 <=> ! [X1,X3,X5,X0,X2,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k2_relset_1(X4,X2,k4_relset_1(X4,X5,X1,X2,X3,X0)) = k2_relat_1(k4_relset_1(X4,X5,X1,X2,X3,X0))) ) | (~spl4_13 | ~spl4_23)),
% 0.21/0.48    inference(resolution,[],[f149,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl4_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f148])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl4_22 | ~spl4_11 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f128,f102,f89,f144])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl4_11 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl4_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_11 | ~spl4_14)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f127])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_11 | ~spl4_14)),
% 0.21/0.48    inference(superposition,[],[f103,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f102])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl4_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f140])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl4_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f136])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl4_19 | ~spl4_2 | ~spl4_4 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f121,f97,f60,f52,f132])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl4_2 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f119,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | (~spl4_4 | ~spl4_13)),
% 0.21/0.48    inference(resolution,[],[f98,f61])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl4_18 | ~spl4_1 | ~spl4_3 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f97,f56,f48,f123])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl4_3 <=> sK0 = k2_relset_1(sK0,sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    sK0 = k2_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f118,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    sK0 = k2_relset_1(sK0,sK0,sK2) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) | (~spl4_1 | ~spl4_13)),
% 0.21/0.48    inference(resolution,[],[f98,f49])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl4_16 | ~spl4_7 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f100,f93,f72,f110])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl4_7 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl4_12 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | (~spl4_7 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f94,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f102])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f97])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl4_12 | ~spl4_5 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f87,f80,f64,f93])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl4_5 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_9 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1))) ) | (~spl4_5 | ~spl4_9)),
% 0.21/0.48    inference(resolution,[],[f81,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f89])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f84])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f80])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f72])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f64])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f60])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f52])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f48])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16088)------------------------------
% 0.21/0.48  % (16088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16088)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16088)Memory used [KB]: 10746
% 0.21/0.48  % (16088)Time elapsed: 0.068 s
% 0.21/0.48  % (16088)------------------------------
% 0.21/0.48  % (16088)------------------------------
% 0.21/0.48  % (16078)Success in time 0.126 s
%------------------------------------------------------------------------------
