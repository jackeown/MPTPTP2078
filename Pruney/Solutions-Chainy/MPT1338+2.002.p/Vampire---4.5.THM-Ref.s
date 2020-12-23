%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  258 ( 645 expanded)
%              Number of leaves         :   57 ( 265 expanded)
%              Depth                    :   10
%              Number of atoms          :  868 (2051 expanded)
%              Number of equality atoms :  150 ( 374 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f121,f125,f131,f135,f139,f143,f149,f176,f180,f190,f205,f212,f219,f223,f239,f249,f257,f261,f302,f311,f315,f316,f359,f418,f419,f437,f445,f446,f475,f484,f489,f490,f500,f539])).

fof(f539,plain,
    ( spl3_54
    | ~ spl3_61 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | spl3_54
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f534,f74])).

fof(f74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f534,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_54
    | ~ spl3_61 ),
    inference(superposition,[],[f432,f499])).

fof(f499,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl3_61
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f432,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl3_54
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f500,plain,
    ( spl3_61
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_21
    | ~ spl3_37
    | ~ spl3_52
    | ~ spl3_55
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f496,f443,f435,f421,f313,f210,f188,f137,f133,f498])).

fof(f133,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f137,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f188,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f210,plain,
    ( spl3_21
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f313,plain,
    ( spl3_37
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f421,plain,
    ( spl3_52
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f435,plain,
    ( spl3_55
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f443,plain,
    ( spl3_57
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f496,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_21
    | ~ spl3_37
    | ~ spl3_52
    | ~ spl3_55
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f464,f495])).

fof(f495,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_21
    | ~ spl3_37
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f494,f422])).

fof(f422,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f421])).

fof(f494,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_21
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f493,f314])).

fof(f314,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f313])).

fof(f493,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_21 ),
    inference(forward_demodulation,[],[f492,f138])).

fof(f138,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f492,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_16
    | spl3_21 ),
    inference(forward_demodulation,[],[f491,f189])).

fof(f189,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f491,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_10
    | spl3_21 ),
    inference(forward_demodulation,[],[f211,f134])).

fof(f134,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f211,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f464,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_55
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f456,f436])).

fof(f436,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f435])).

fof(f456,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_57 ),
    inference(resolution,[],[f444,f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f444,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f443])).

fof(f490,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f489,plain,
    ( spl3_60
    | ~ spl3_26
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f467,f443,f247,f487])).

fof(f487,plain,
    ( spl3_60
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f247,plain,
    ( spl3_26
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f467,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_26
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f458,f248])).

fof(f248,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f247])).

fof(f458,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_57 ),
    inference(resolution,[],[f444,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f484,plain,
    ( ~ spl3_54
    | ~ spl3_6
    | spl3_22
    | ~ spl3_28
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f482,f473,f443,f255,f217,f116,f431])).

fof(f116,plain,
    ( spl3_6
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f217,plain,
    ( spl3_22
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f255,plain,
    ( spl3_28
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f473,plain,
    ( spl3_58
  <=> v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f482,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl3_6
    | spl3_22
    | ~ spl3_28
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f480,f481])).

fof(f481,plain,
    ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_28
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f283,f474])).

fof(f474,plain,
    ( v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f473])).

fof(f283,plain,
    ( ~ v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f282,f117])).

fof(f117,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f282,plain,
    ( ~ v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_28 ),
    inference(superposition,[],[f84,f256])).

fof(f256,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f84,plain,(
    ! [X1] :
      ( ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v1_partfun1(X1,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) != X0
      | v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f480,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | spl3_22
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f461,f218])).

fof(f218,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f461,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_57 ),
    inference(resolution,[],[f444,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f475,plain,
    ( spl3_58
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f462,f443,f473])).

fof(f462,plain,
    ( v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_57 ),
    inference(resolution,[],[f444,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f446,plain,
    ( spl3_52
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_29
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f393,f357,f313,f309,f259,f188,f90,f86,f421])).

fof(f86,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f259,plain,
    ( spl3_29
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f309,plain,
    ( spl3_36
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f357,plain,
    ( spl3_42
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f393,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_29
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f392,f91])).

fof(f91,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f392,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_16
    | ~ spl3_29
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f349,f361])).

fof(f361,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_16
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f360,f314])).

fof(f360,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_16
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f358,f189])).

fof(f358,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f357])).

fof(f349,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_29
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f348,f87])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f348,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_29
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f340,f260])).

fof(f260,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f259])).

fof(f340,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_36 ),
    inference(resolution,[],[f310,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f310,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f309])).

fof(f445,plain,
    ( spl3_57
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f235,f203,f147,f116,f90,f86,f443])).

fof(f147,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f203,plain,
    ( spl3_19
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f235,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f234,f171])).

fof(f171,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f111,f167])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f158,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f158,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f148,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f109,f87])).

fof(f109,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f234,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f233,f170])).

fof(f170,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f112,f167])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f110,f87])).

fof(f110,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f91,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f233,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f227,f117])).

fof(f227,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_19 ),
    inference(resolution,[],[f204,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f204,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f437,plain,
    ( spl3_55
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f232,f203,f147,f116,f90,f86,f435])).

fof(f232,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f231,f171])).

fof(f231,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f230,f170])).

fof(f230,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f226,f117])).

fof(f226,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_19 ),
    inference(resolution,[],[f204,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f419,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f418,plain,
    ( spl3_51
    | ~ spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f162,f147,f129,f90,f86,f182,f415])).

fof(f415,plain,
    ( spl3_51
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f182,plain,
    ( spl3_15
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f129,plain,
    ( spl3_9
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f162,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f161,f91])).

fof(f161,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f160,f87])).

fof(f160,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f152,f130])).

fof(f130,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f152,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f148,f60])).

fof(f359,plain,
    ( spl3_42
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f153,f147,f357])).

fof(f153,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f148,f65])).

fof(f316,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f315,plain,
    ( spl3_37
    | ~ spl3_7
    | ~ spl3_24
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f307,f297,f237,f119,f313])).

fof(f119,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f237,plain,
    ( spl3_24
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f297,plain,
    ( spl3_34
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f307,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_24
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f306,f175])).

fof(f175,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f306,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f305,f238])).

fof(f238,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f237])).

fof(f305,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_34 ),
    inference(resolution,[],[f298,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f298,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f297])).

fof(f311,plain,
    ( spl3_36
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f172,f147,f86,f309])).

% (7070)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f108,f167])).

fof(f108,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f71])).

fof(f302,plain,
    ( spl3_34
    | spl3_35
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f166,f147,f129,f86,f300,f297])).

fof(f300,plain,
    ( spl3_35
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f166,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f165,f130])).

fof(f165,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f155,f87])).

fof(f155,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f148,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f261,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f173,f147,f86,f259])).

fof(f173,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f107,f167])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f70])).

fof(f257,plain,
    ( spl3_28
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f171,f147,f90,f86,f255])).

% (7072)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f249,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f170,f147,f90,f86,f247])).

fof(f239,plain,
    ( spl3_24
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f157,f147,f237])).

fof(f157,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f148,f78])).

fof(f223,plain,
    ( ~ spl3_23
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_20 ),
    inference(avatar_split_clause,[],[f215,f207,f188,f137,f133,f221])).

fof(f221,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f207,plain,
    ( spl3_20
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f215,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_20 ),
    inference(forward_demodulation,[],[f214,f138])).

fof(f214,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_16
    | spl3_20 ),
    inference(forward_demodulation,[],[f213,f189])).

fof(f213,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_10
    | spl3_20 ),
    inference(forward_demodulation,[],[f208,f134])).

fof(f208,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f219,plain,
    ( ~ spl3_22
    | spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f201,f188,f98,f94,f217])).

fof(f94,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f98,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f201,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f200,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f200,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f199,f99])).

fof(f99,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f199,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f63,f189])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f212,plain,
    ( ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f45,f210,f207])).

fof(f45,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f205,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f174,f147,f86,f203])).

fof(f174,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f106,f167])).

fof(f106,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f190,plain,
    ( spl3_16
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f186,f178,f147,f137,f133,f188])).

fof(f178,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f186,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f185,f153])).

fof(f185,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f184,f138])).

fof(f184,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f179,f134])).

fof(f179,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f49,f178])).

fof(f49,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f176,plain,
    ( spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f167,f147,f119])).

fof(f149,plain,
    ( spl3_13
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f145,f141,f137,f133,f147])).

fof(f141,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f144,f138])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f142,f134])).

fof(f142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f48,f141])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f139,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f114,f102,f137])).

fof(f102,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f114,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f103,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f103,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f135,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f113,f98,f133])).

fof(f113,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f99,f64])).

fof(f131,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f127,f123,f102,f98,f129])).

fof(f123,plain,
    ( spl3_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f126,f114])).

fof(f126,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f124,f113])).

fof(f124,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f47,f123])).

fof(f47,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f121,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f105,f86,f119,f116])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f94])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f50,f90])).

fof(f50,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

% (7074)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (7075)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (7061)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (7066)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (7077)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f88,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (7063)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (7060)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (7071)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (7071)Refutation not found, incomplete strategy% (7071)------------------------------
% 0.22/0.49  % (7071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7071)Memory used [KB]: 1663
% 0.22/0.49  % (7071)Time elapsed: 0.071 s
% 0.22/0.49  % (7071)------------------------------
% 0.22/0.49  % (7071)------------------------------
% 0.22/0.49  % (7068)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (7064)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (7067)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (7065)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (7062)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (7059)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (7076)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (7058)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (7073)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (7059)Refutation not found, incomplete strategy% (7059)------------------------------
% 0.22/0.52  % (7059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7059)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7059)Memory used [KB]: 10746
% 0.22/0.52  % (7059)Time elapsed: 0.092 s
% 0.22/0.52  % (7059)------------------------------
% 0.22/0.52  % (7059)------------------------------
% 0.22/0.52  % (7078)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (7078)Refutation not found, incomplete strategy% (7078)------------------------------
% 0.22/0.52  % (7078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7078)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7078)Memory used [KB]: 10618
% 0.22/0.52  % (7078)Time elapsed: 0.097 s
% 0.22/0.52  % (7078)------------------------------
% 0.22/0.52  % (7078)------------------------------
% 0.22/0.52  % (7058)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f540,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f121,f125,f131,f135,f139,f143,f149,f176,f180,f190,f205,f212,f219,f223,f239,f249,f257,f261,f302,f311,f315,f316,f359,f418,f419,f437,f445,f446,f475,f484,f489,f490,f500,f539])).
% 0.22/0.52  fof(f539,plain,(
% 0.22/0.52    spl3_54 | ~spl3_61),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f538])).
% 0.22/0.52  fof(f538,plain,(
% 0.22/0.52    $false | (spl3_54 | ~spl3_61)),
% 0.22/0.52    inference(subsumption_resolution,[],[f534,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f534,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | (spl3_54 | ~spl3_61)),
% 0.22/0.52    inference(superposition,[],[f432,f499])).
% 0.22/0.52  fof(f499,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_61),
% 0.22/0.52    inference(avatar_component_clause,[],[f498])).
% 0.22/0.52  fof(f498,plain,(
% 0.22/0.52    spl3_61 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.22/0.52  fof(f432,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_relat_1(sK2)) | spl3_54),
% 0.22/0.52    inference(avatar_component_clause,[],[f431])).
% 0.22/0.52  fof(f431,plain,(
% 0.22/0.52    spl3_54 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.52  fof(f500,plain,(
% 0.22/0.52    spl3_61 | ~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_21 | ~spl3_37 | ~spl3_52 | ~spl3_55 | ~spl3_57),
% 0.22/0.52    inference(avatar_split_clause,[],[f496,f443,f435,f421,f313,f210,f188,f137,f133,f498])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl3_10 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    spl3_16 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    spl3_21 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    spl3_37 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.52  fof(f421,plain,(
% 0.22/0.52    spl3_52 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.22/0.52  fof(f435,plain,(
% 0.22/0.52    spl3_55 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.52  fof(f443,plain,(
% 0.22/0.52    spl3_57 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.52  fof(f496,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | (~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_21 | ~spl3_37 | ~spl3_52 | ~spl3_55 | ~spl3_57)),
% 0.22/0.52    inference(subsumption_resolution,[],[f464,f495])).
% 0.22/0.52  fof(f495,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_21 | ~spl3_37 | ~spl3_52)),
% 0.22/0.52    inference(forward_demodulation,[],[f494,f422])).
% 0.22/0.52  fof(f422,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_52),
% 0.22/0.52    inference(avatar_component_clause,[],[f421])).
% 0.22/0.52  fof(f494,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_21 | ~spl3_37)),
% 0.22/0.52    inference(forward_demodulation,[],[f493,f314])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f313])).
% 0.22/0.52  fof(f493,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f492,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f137])).
% 0.22/0.52  fof(f492,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_16 | spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f491,f189])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f188])).
% 0.22/0.52  fof(f491,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_10 | spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f211,f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f133])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f210])).
% 0.22/0.52  fof(f464,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_55 | ~spl3_57)),
% 0.22/0.52    inference(subsumption_resolution,[],[f456,f436])).
% 0.22/0.52  fof(f436,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_55),
% 0.22/0.52    inference(avatar_component_clause,[],[f435])).
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_57),
% 0.22/0.52    inference(resolution,[],[f444,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f444,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_57),
% 0.22/0.52    inference(avatar_component_clause,[],[f443])).
% 0.22/0.52  fof(f490,plain,(
% 0.22/0.52    k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relat_1(sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f489,plain,(
% 0.22/0.52    spl3_60 | ~spl3_26 | ~spl3_57),
% 0.22/0.52    inference(avatar_split_clause,[],[f467,f443,f247,f487])).
% 0.22/0.52  fof(f487,plain,(
% 0.22/0.52    spl3_60 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    spl3_26 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.52  fof(f467,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_26 | ~spl3_57)),
% 0.22/0.52    inference(forward_demodulation,[],[f458,f248])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f247])).
% 0.22/0.52  fof(f458,plain,(
% 0.22/0.52    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_57),
% 0.22/0.52    inference(resolution,[],[f444,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f484,plain,(
% 0.22/0.52    ~spl3_54 | ~spl3_6 | spl3_22 | ~spl3_28 | ~spl3_57 | ~spl3_58),
% 0.22/0.52    inference(avatar_split_clause,[],[f482,f473,f443,f255,f217,f116,f431])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    spl3_6 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    spl3_22 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    spl3_28 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.52  fof(f473,plain,(
% 0.22/0.52    spl3_58 <=> v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.52  fof(f482,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_relat_1(sK2)) | (~spl3_6 | spl3_22 | ~spl3_28 | ~spl3_57 | ~spl3_58)),
% 0.22/0.52    inference(subsumption_resolution,[],[f480,f481])).
% 0.22/0.52  fof(f481,plain,(
% 0.22/0.52    v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | (~spl3_6 | ~spl3_28 | ~spl3_58)),
% 0.22/0.52    inference(subsumption_resolution,[],[f283,f474])).
% 0.22/0.52  fof(f474,plain,(
% 0.22/0.52    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_58),
% 0.22/0.52    inference(avatar_component_clause,[],[f473])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    ~v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | (~spl3_6 | ~spl3_28)),
% 0.22/0.52    inference(subsumption_resolution,[],[f282,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f116])).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    ~v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_28),
% 0.22/0.52    inference(superposition,[],[f84,f256])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f255])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X1] : (~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1) | v1_partfun1(X1,k1_relat_1(X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) != X0 | v1_partfun1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.52  fof(f480,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_relat_1(sK2)) | ~v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | (spl3_22 | ~spl3_57)),
% 0.22/0.52    inference(subsumption_resolution,[],[f461,f218])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f217])).
% 0.22/0.52  fof(f461,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_57),
% 0.22/0.52    inference(resolution,[],[f444,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_partfun1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.22/0.52  fof(f475,plain,(
% 0.22/0.52    spl3_58 | ~spl3_57),
% 0.22/0.52    inference(avatar_split_clause,[],[f462,f443,f473])).
% 0.22/0.52  fof(f462,plain,(
% 0.22/0.52    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_57),
% 0.22/0.52    inference(resolution,[],[f444,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f446,plain,(
% 0.22/0.52    spl3_52 | ~spl3_1 | ~spl3_2 | ~spl3_16 | ~spl3_29 | ~spl3_36 | ~spl3_37 | ~spl3_42),
% 0.22/0.52    inference(avatar_split_clause,[],[f393,f357,f313,f309,f259,f188,f90,f86,f421])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    spl3_29 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.52  fof(f309,plain,(
% 0.22/0.52    spl3_36 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.52  fof(f357,plain,(
% 0.22/0.52    spl3_42 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.22/0.52  fof(f393,plain,(
% 0.22/0.52    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_16 | ~spl3_29 | ~spl3_36 | ~spl3_37 | ~spl3_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f392,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f90])).
% 0.22/0.52  fof(f392,plain,(
% 0.22/0.52    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_16 | ~spl3_29 | ~spl3_36 | ~spl3_37 | ~spl3_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f349,f361])).
% 0.22/0.52  fof(f361,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_16 | ~spl3_37 | ~spl3_42)),
% 0.22/0.52    inference(forward_demodulation,[],[f360,f314])).
% 0.22/0.52  fof(f360,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_16 | ~spl3_42)),
% 0.22/0.52    inference(forward_demodulation,[],[f358,f189])).
% 0.22/0.52  fof(f358,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f357])).
% 0.22/0.52  fof(f349,plain,(
% 0.22/0.52    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_29 | ~spl3_36)),
% 0.22/0.52    inference(subsumption_resolution,[],[f348,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f86])).
% 0.22/0.52  fof(f348,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_29 | ~spl3_36)),
% 0.22/0.52    inference(subsumption_resolution,[],[f340,f260])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_29),
% 0.22/0.52    inference(avatar_component_clause,[],[f259])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_36),
% 0.22/0.52    inference(resolution,[],[f310,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f309])).
% 0.22/0.52  fof(f445,plain,(
% 0.22/0.52    spl3_57 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_13 | ~spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f235,f203,f147,f116,f90,f86,f443])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    spl3_19 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_13 | ~spl3_19)),
% 0.22/0.52    inference(forward_demodulation,[],[f234,f171])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f111,f167])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl3_13),
% 0.22/0.52    inference(subsumption_resolution,[],[f158,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f148,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f147])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f109,f87])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f91,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_13 | ~spl3_19)),
% 0.22/0.52    inference(forward_demodulation,[],[f233,f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f112,f167])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f110,f87])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f91,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_6 | ~spl3_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f227,f117])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_19),
% 0.22/0.52    inference(resolution,[],[f204,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK2)) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f203])).
% 0.22/0.52  fof(f437,plain,(
% 0.22/0.52    spl3_55 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_13 | ~spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f232,f203,f147,f116,f90,f86,f435])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_13 | ~spl3_19)),
% 0.22/0.52    inference(forward_demodulation,[],[f231,f171])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_13 | ~spl3_19)),
% 0.22/0.52    inference(forward_demodulation,[],[f230,f170])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_6 | ~spl3_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f226,f117])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_19),
% 0.22/0.52    inference(resolution,[],[f204,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f419,plain,(
% 0.22/0.52    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f418,plain,(
% 0.22/0.52    spl3_51 | ~spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f162,f147,f129,f90,f86,f182,f415])).
% 0.22/0.52  fof(f415,plain,(
% 0.22/0.52    spl3_51 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    spl3_15 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl3_9 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f161,f91])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f160,f87])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_9 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f152,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f148,f60])).
% 0.22/0.52  fof(f359,plain,(
% 0.22/0.52    spl3_42 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f153,f147,f357])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f148,f65])).
% 0.22/0.52  fof(f316,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k2_relat_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    spl3_37 | ~spl3_7 | ~spl3_24 | ~spl3_34),
% 0.22/0.52    inference(avatar_split_clause,[],[f307,f297,f237,f119,f313])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl3_7 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    spl3_24 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.52  fof(f297,plain,(
% 0.22/0.52    spl3_34 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.52  fof(f307,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_7 | ~spl3_24 | ~spl3_34)),
% 0.22/0.52    inference(subsumption_resolution,[],[f306,f175])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  fof(f306,plain,(
% 0.22/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_24 | ~spl3_34)),
% 0.22/0.52    inference(subsumption_resolution,[],[f305,f238])).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f237])).
% 0.22/0.52  fof(f305,plain,(
% 0.22/0.52    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_34),
% 0.22/0.52    inference(resolution,[],[f298,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_34),
% 0.22/0.52    inference(avatar_component_clause,[],[f297])).
% 0.22/0.52  fof(f311,plain,(
% 0.22/0.52    spl3_36 | ~spl3_1 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f172,f147,f86,f309])).
% 0.22/0.52  % (7070)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f167])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f87,f71])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    spl3_34 | spl3_35 | ~spl3_1 | ~spl3_9 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f166,f147,f129,f86,f300,f297])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    spl3_35 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f165,f130])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f87])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f148,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.52    inference(flattening,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    spl3_29 | ~spl3_1 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f173,f147,f86,f259])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f107,f167])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f87,f70])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    spl3_28 | ~spl3_1 | ~spl3_2 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f171,f147,f90,f86,f255])).
% 0.22/0.52  % (7072)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    spl3_26 | ~spl3_1 | ~spl3_2 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f170,f147,f90,f86,f247])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    spl3_24 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f157,f147,f237])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f148,f78])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ~spl3_23 | ~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f215,f207,f188,f137,f133,f221])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    spl3_23 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    spl3_20 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_20)),
% 0.22/0.52    inference(forward_demodulation,[],[f214,f138])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_16 | spl3_20)),
% 0.22/0.52    inference(forward_demodulation,[],[f213,f189])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_10 | spl3_20)),
% 0.22/0.52    inference(forward_demodulation,[],[f208,f134])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f207])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    ~spl3_22 | spl3_3 | ~spl3_4 | ~spl3_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f201,f188,f98,f94,f217])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl3_3 <=> v2_struct_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl3_4 <=> l1_struct_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f200,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ~v2_struct_0(sK1) | spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f94])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f199,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    l1_struct_0(sK1) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f98])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_16),
% 0.22/0.52    inference(superposition,[],[f63,f189])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    ~spl3_20 | ~spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f210,f207])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f17])).
% 0.22/0.52  fof(f17,conjecture,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    spl3_19 | ~spl3_1 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f174,f147,f86,f203])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f106,f167])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f87,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    spl3_16 | ~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f186,f178,f147,f137,f133,f188])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f185,f153])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_10 | ~spl3_11 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f184,f138])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_10 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f179,f134])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f178])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f49,f178])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    spl3_7 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f167,f147,f119])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl3_13 | ~spl3_10 | ~spl3_11 | ~spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f145,f141,f137,f133,f147])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_10 | ~spl3_11 | ~spl3_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f144,f138])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_10 | ~spl3_12)),
% 0.22/0.52    inference(forward_demodulation,[],[f142,f134])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f141])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f141])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl3_11 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f114,f102,f137])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl3_5 <=> l1_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.52    inference(resolution,[],[f103,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    l1_struct_0(sK0) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl3_10 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f98,f133])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.22/0.52    inference(resolution,[],[f99,f64])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl3_9 | ~spl3_4 | ~spl3_5 | ~spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f123,f102,f98,f129])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl3_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_8)),
% 0.22/0.52    inference(forward_demodulation,[],[f126,f114])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_8)),
% 0.22/0.52    inference(forward_demodulation,[],[f124,f113])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f123])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f123])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl3_6 | ~spl3_7 | ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f86,f119,f116])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f87,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f53,f102])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    l1_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f98])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    l1_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ~spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f51,f94])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f50,f90])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  % (7074)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (7075)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (7061)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (7066)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.36/0.53  % (7077)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.36/0.54  fof(f88,plain,(
% 1.36/0.54    spl3_1),
% 1.36/0.54    inference(avatar_split_clause,[],[f46,f86])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    v1_funct_1(sK2)),
% 1.36/0.54    inference(cnf_transformation,[],[f21])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (7058)------------------------------
% 1.36/0.54  % (7058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (7058)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (7058)Memory used [KB]: 6524
% 1.36/0.54  % (7058)Time elapsed: 0.097 s
% 1.36/0.54  % (7058)------------------------------
% 1.36/0.54  % (7058)------------------------------
% 1.36/0.54  % (7057)Success in time 0.175 s
%------------------------------------------------------------------------------
