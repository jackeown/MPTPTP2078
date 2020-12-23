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
% DateTime   : Thu Dec  3 13:14:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 309 expanded)
%              Number of leaves         :   40 ( 131 expanded)
%              Depth                    :   11
%              Number of atoms          :  510 (1048 expanded)
%              Number of equality atoms :  111 ( 258 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f92,f97,f102,f107,f112,f133,f139,f148,f149,f163,f168,f178,f184,f189,f202,f209,f218,f223,f227,f286,f287,f288])).

fof(f288,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f287,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f286,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f270,f215,f175,f136,f114,f62,f57,f283])).

fof(f283,plain,
    ( spl3_34
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f57,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f62,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f114,plain,
    ( spl3_11
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f136,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f175,plain,
    ( spl3_19
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f215,plain,
    ( spl3_25
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f270,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f254,f217])).

fof(f217,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f215])).

fof(f254,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f253,f116])).

fof(f116,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f253,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f252,f177])).

fof(f177,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f175])).

fof(f252,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(resolution,[],[f84,f138])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f59,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_1(sK2)
        | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f64,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f227,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f225,f69])).

fof(f69,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f225,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f224,f74])).

fof(f74,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f224,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_23 ),
    inference(resolution,[],[f201,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f201,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_23
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f223,plain,
    ( spl3_26
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f213,f186,f181,f136,f220])).

fof(f220,plain,
    ( spl3_26
  <=> k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f181,plain,
    ( spl3_20
  <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f186,plain,
    ( spl3_21
  <=> k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f213,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f212,f183])).

fof(f183,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f212,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f146,f188])).

fof(f188,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f146,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_14 ),
    inference(resolution,[],[f138,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(f218,plain,
    ( spl3_25
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f211,f195,f165,f130,f215])).

fof(f130,plain,
    ( spl3_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f165,plain,
    ( spl3_17
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f195,plain,
    ( spl3_22
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f211,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f210,f167])).

fof(f167,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f210,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(resolution,[],[f197,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl3_13 ),
    inference(resolution,[],[f131,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f131,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f197,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f209,plain,
    ( spl3_24
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f204,f186,f136,f114,f206])).

fof(f206,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f204,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f203,f116])).

fof(f203,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f145,f188])).

fof(f145,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_14 ),
    inference(resolution,[],[f138,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f202,plain,
    ( spl3_22
    | spl3_23
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f193,f175,f136,f57,f199,f195])).

fof(f193,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f192,f177])).

fof(f192,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(resolution,[],[f81,f138])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f189,plain,
    ( spl3_21
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f179,f136,f126,f186])).

fof(f126,plain,
    ( spl3_12
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f179,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f141,f128])).

fof(f128,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f141,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f138,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f184,plain,
    ( spl3_20
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f142,f136,f181])).

fof(f142,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f138,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f178,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f121,f104,f94,f89,f175])).

fof(f89,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( spl3_7
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f104,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f121,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f120,f96])).

fof(f96,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f120,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f91,f106])).

fof(f106,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f91,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f168,plain,
    ( spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f143,f136,f165])).

fof(f143,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f138,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f163,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f154,f104,f94,f160,f156])).

fof(f156,plain,
    ( spl3_15
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f160,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f154,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f153,f106])).

fof(f153,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f152,f96])).

fof(f152,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f151,f106])).

fof(f151,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f32,f96])).

fof(f32,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f149,plain,
    ( spl3_11
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f124,f109,f104,f94,f114])).

fof(f109,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f119,f106])).

fof(f119,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f111,f96])).

fof(f111,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f148,plain,
    ( spl3_13
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f140,f132])).

fof(f132,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f140,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f139,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f122,f104,f99,f94,f136])).

fof(f99,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f122,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f118,f106])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f101,f96])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f133,plain,
    ( spl3_12
    | ~ spl3_13
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f85,f62,f57,f130,f126])).

fof(f85,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f83,f59])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f112,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f36,f109])).

fof(f36,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f87,f77,f104])).

fof(f77,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f87,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f79,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f102,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f35,f99])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f86,f72,f94])).

fof(f86,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f74,f41])).

fof(f92,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:03:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (22765)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (22774)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (22767)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (22772)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (22772)Refutation not found, incomplete strategy% (22772)------------------------------
% 0.22/0.49  % (22772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22772)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22772)Memory used [KB]: 6012
% 0.22/0.49  % (22772)Time elapsed: 0.002 s
% 0.22/0.49  % (22772)------------------------------
% 0.22/0.49  % (22772)------------------------------
% 0.22/0.50  % (22773)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (22761)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (22760)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (22779)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (22775)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (22763)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (22773)Refutation not found, incomplete strategy% (22773)------------------------------
% 0.22/0.52  % (22773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22773)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22773)Memory used [KB]: 1663
% 0.22/0.52  % (22773)Time elapsed: 0.084 s
% 0.22/0.52  % (22773)------------------------------
% 0.22/0.52  % (22773)------------------------------
% 0.22/0.52  % (22764)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (22780)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (22763)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f289,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f92,f97,f102,f107,f112,f133,f139,f148,f149,f163,f168,f178,f184,f189,f202,f209,f218,f223,f227,f286,f287,f288])).
% 0.22/0.52  fof(f288,plain,(
% 0.22/0.52    k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    spl3_34 | ~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_14 | ~spl3_19 | ~spl3_25),
% 0.22/0.52    inference(avatar_split_clause,[],[f270,f215,f175,f136,f114,f62,f57,f283])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    spl3_34 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl3_11 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    spl3_19 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    spl3_25 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_14 | ~spl3_19 | ~spl3_25)),
% 0.22/0.52    inference(forward_demodulation,[],[f254,f217])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f215])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_14 | ~spl3_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f253,f116])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f114])).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f252,f177])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f175])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14)),
% 0.22/0.52    inference(resolution,[],[f84,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f136])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f82,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)) ) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f64,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    spl3_3 | ~spl3_4 | ~spl3_23),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f226])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    $false | (spl3_3 | ~spl3_4 | ~spl3_23)),
% 0.22/0.52    inference(subsumption_resolution,[],[f225,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ~v2_struct_0(sK1) | spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl3_3 <=> v2_struct_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    v2_struct_0(sK1) | (~spl3_4 | ~spl3_23)),
% 0.22/0.52    inference(subsumption_resolution,[],[f224,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    l1_struct_0(sK1) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl3_4 <=> l1_struct_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_23),
% 0.22/0.52    inference(resolution,[],[f201,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f199])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    spl3_23 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    spl3_26 | ~spl3_14 | ~spl3_20 | ~spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f213,f186,f181,f136,f220])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    spl3_26 <=> k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    spl3_20 <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    spl3_21 <=> k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_14 | ~spl3_20 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f212,f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f181])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_14 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f146,f188])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f186])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f138,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    spl3_25 | ~spl3_13 | ~spl3_17 | ~spl3_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f211,f195,f165,f130,f215])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    spl3_13 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    spl3_17 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    spl3_22 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_13 | ~spl3_17 | ~spl3_22)),
% 0.22/0.52    inference(subsumption_resolution,[],[f210,f167])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f165])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | (~spl3_13 | ~spl3_22)),
% 0.22/0.52    inference(resolution,[],[f197,f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0)) ) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f131,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f130])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f195])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    spl3_24 | ~spl3_11 | ~spl3_14 | ~spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f204,f186,f136,f114,f206])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    spl3_24 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_11 | ~spl3_14 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f203,f116])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_14 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f145,f188])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f138,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    spl3_22 | spl3_23 | ~spl3_1 | ~spl3_14 | ~spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f193,f175,f136,f57,f199,f195])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14 | ~spl3_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f192,f177])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14)),
% 0.22/0.52    inference(resolution,[],[f81,f138])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f59,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    spl3_21 | ~spl3_12 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f179,f136,f126,f186])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl3_12 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_12 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f141,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f126])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f138,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    spl3_20 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f142,f136,f181])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f138,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    spl3_19 | ~spl3_6 | ~spl3_7 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f121,f104,f94,f89,f175])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl3_7 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f120,f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f94])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_6 | ~spl3_9)),
% 0.22/0.52    inference(superposition,[],[f91,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f104])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    spl3_17 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f143,f136,f165])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f138,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ~spl3_15 | ~spl3_16 | ~spl3_7 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f154,f104,f94,f160,f156])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    spl3_15 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    spl3_16 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f153,f106])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f152,f96])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f151,f106])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl3_7),
% 0.22/0.52    inference(forward_demodulation,[],[f32,f96])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl3_11 | ~spl3_7 | ~spl3_9 | ~spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f124,f109,f104,f94,f114])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl3_10 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f119,f106])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f111,f96])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f109])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl3_13 | ~spl3_14),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f147])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    $false | (spl3_13 | ~spl3_14)),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f130])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f138,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl3_14 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f122,f104,f99,f94,f136])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f118,f106])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.22/0.52    inference(forward_demodulation,[],[f101,f96])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f99])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl3_12 | ~spl3_13 | ~spl3_1 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f85,f62,f57,f130,f126])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f59])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f64,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = k4_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f36,f109])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl3_9 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f87,f77,f104])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl3_5 <=> l1_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.52    inference(resolution,[],[f79,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    l1_struct_0(sK0) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f99])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl3_7 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f86,f72,f94])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f74,f41])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f34,f89])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f40,f77])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    l1_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f39,f72])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    l1_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ~spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f38,f67])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f37,f62])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f33,f57])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (22763)------------------------------
% 0.22/0.52  % (22763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22763)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (22763)Memory used [KB]: 10746
% 0.22/0.52  % (22763)Time elapsed: 0.102 s
% 0.22/0.52  % (22763)------------------------------
% 0.22/0.52  % (22763)------------------------------
% 0.22/0.52  % (22780)Refutation not found, incomplete strategy% (22780)------------------------------
% 0.22/0.52  % (22780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22780)Memory used [KB]: 10618
% 0.22/0.52  % (22780)Time elapsed: 0.118 s
% 0.22/0.52  % (22780)------------------------------
% 0.22/0.52  % (22780)------------------------------
% 0.22/0.53  % (22759)Success in time 0.159 s
%------------------------------------------------------------------------------
