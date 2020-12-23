%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 527 expanded)
%              Number of leaves         :   66 ( 231 expanded)
%              Depth                    :   10
%              Number of atoms          :  836 (1705 expanded)
%              Number of equality atoms :  164 ( 335 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f115,f119,f125,f129,f133,f137,f143,f173,f177,f191,f210,f217,f224,f228,f236,f261,f272,f277,f278,f288,f349,f358,f379,f398,f399,f431,f457,f475,f501,f504,f505,f539,f548,f558,f574,f590,f591,f592])).

fof(f592,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k1_relat_1(k2_funct_1(sK2)) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f591,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2)))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f590,plain,
    ( spl3_83
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f441,f429,f588])).

fof(f588,plain,
    ( spl3_83
  <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f429,plain,
    ( spl3_55
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f441,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_55 ),
    inference(resolution,[],[f430,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f430,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f429])).

fof(f574,plain,
    ( spl3_81
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f436,f429,f572])).

fof(f572,plain,
    ( spl3_81
  <=> k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f436,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_55 ),
    inference(resolution,[],[f430,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f558,plain,
    ( spl3_77
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f494,f473,f141,f88,f84,f556])).

fof(f556,plain,
    ( spl3_77
  <=> k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f84,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f141,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f473,plain,
    ( spl3_60
  <=> k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f494,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_60 ),
    inference(superposition,[],[f474,f170])).

fof(f170,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f106,f167])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f152,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f142,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f105,f85])).

fof(f85,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f89,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f89,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f474,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f473])).

fof(f548,plain,
    ( spl3_74
    | ~ spl3_6
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f544,f459,f455,f110,f546])).

fof(f546,plain,
    ( spl3_74
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f110,plain,
    ( spl3_6
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f455,plain,
    ( spl3_57
  <=> v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f459,plain,
    ( spl3_58
  <=> v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f544,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f543,f111])).

fof(f111,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f543,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f542,f456])).

fof(f456,plain,
    ( v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f455])).

fof(f542,plain,
    ( ~ v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_58 ),
    inference(resolution,[],[f460,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f460,plain,
    ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f459])).

fof(f539,plain,
    ( ~ spl3_52
    | ~ spl3_7
    | spl3_53 ),
    inference(avatar_split_clause,[],[f419,f416,f113,f413])).

fof(f413,plain,
    ( spl3_52
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f113,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f416,plain,
    ( spl3_53
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f419,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_7
    | spl3_53 ),
    inference(subsumption_resolution,[],[f187,f417])).

fof(f417,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_53 ),
    inference(avatar_component_clause,[],[f416])).

fof(f187,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f172,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f505,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f504,plain,
    ( ~ spl3_49
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl3_49
    | spl3_52 ),
    inference(subsumption_resolution,[],[f502,f420])).

fof(f420,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_52 ),
    inference(avatar_component_clause,[],[f413])).

fof(f502,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_49 ),
    inference(resolution,[],[f500,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f500,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl3_49
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f501,plain,
    ( spl3_58
    | spl3_49
    | ~ spl3_19
    | ~ spl3_50
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f463,f429,f396,f208,f392,f459])).

fof(f208,plain,
    ( spl3_19
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f396,plain,
    ( spl3_50
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f463,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_19
    | ~ spl3_50
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f462,f397])).

fof(f397,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f396])).

fof(f462,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_19
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f442,f209])).

fof(f209,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f442,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_55 ),
    inference(resolution,[],[f430,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f475,plain,
    ( spl3_60
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f199,f110,f473])).

fof(f199,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_6 ),
    inference(resolution,[],[f111,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f457,plain,
    ( spl3_57
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f443,f429,f455])).

fof(f443,plain,
    ( v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_55 ),
    inference(resolution,[],[f430,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f431,plain,
    ( spl3_55
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f319,f286,f283,f275,f189,f123,f88,f84,f429])).

fof(f123,plain,
    ( spl3_9
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f189,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f275,plain,
    ( spl3_31
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f283,plain,
    ( spl3_33
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f286,plain,
    ( spl3_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f319,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f318,f284])).

fof(f284,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f283])).

fof(f318,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f317,f89])).

fof(f317,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f316,f85])).

fof(f316,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f303,f296])).

fof(f296,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f289,f190])).

fof(f190,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f289,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(superposition,[],[f124,f276])).

fof(f276,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f275])).

fof(f124,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f303,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_34 ),
    inference(resolution,[],[f287,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f287,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f286])).

% (5615)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f399,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f398,plain,
    ( spl3_50
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f315,f286,f283,f275,f189,f123,f88,f84,f396])).

fof(f315,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f314,f284])).

fof(f314,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f313,f89])).

fof(f313,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f312,f85])).

fof(f312,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f302,f296])).

fof(f302,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_34 ),
    inference(resolution,[],[f287,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f379,plain,
    ( spl3_45
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f184,f113,f377])).

fof(f377,plain,
    ( spl3_45
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f184,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_7 ),
    inference(resolution,[],[f172,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f358,plain,
    ( spl3_41
    | ~ spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f155,f141,f123,f88,f84,f179,f356])).

fof(f356,plain,
    ( spl3_41
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f179,plain,
    ( spl3_15
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f155,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f154,f89])).

fof(f154,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f153,f85])).

fof(f153,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f145,f124])).

fof(f145,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f142,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f349,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f288,plain,
    ( spl3_34
    | ~ spl3_7
    | ~ spl3_24
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f273,f270,f256,f234,f113,f286])).

fof(f234,plain,
    ( spl3_24
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f256,plain,
    ( spl3_28
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f270,plain,
    ( spl3_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f273,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_24
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f271,f264])).

fof(f264,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f263,f172])).

fof(f263,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f262,f235])).

fof(f235,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f234])).

fof(f262,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_28 ),
    inference(resolution,[],[f257,f79])).

fof(f257,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f256])).

fof(f271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f278,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f277,plain,
    ( spl3_31
    | ~ spl3_7
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f264,f256,f234,f113,f275])).

fof(f272,plain,
    ( spl3_30
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f202,f189,f141,f270])).

fof(f202,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(superposition,[],[f142,f190])).

fof(f261,plain,
    ( spl3_28
    | spl3_29
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f166,f141,f123,f84,f259,f256])).

fof(f259,plain,
    ( spl3_29
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f166,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f165,f124])).

fof(f165,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f150,f85])).

fof(f150,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f142,f69])).

fof(f236,plain,
    ( spl3_24
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f151,f141,f234])).

fof(f151,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f142,f81])).

fof(f228,plain,
    ( ~ spl3_23
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_20 ),
    inference(avatar_split_clause,[],[f220,f212,f189,f131,f127,f226])).

fof(f226,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f127,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f131,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f212,plain,
    ( spl3_20
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f220,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_16
    | spl3_20 ),
    inference(forward_demodulation,[],[f219,f132])).

fof(f132,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f219,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_10
    | ~ spl3_16
    | spl3_20 ),
    inference(forward_demodulation,[],[f218,f190])).

fof(f218,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_10
    | spl3_20 ),
    inference(forward_demodulation,[],[f213,f128])).

fof(f128,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f213,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f224,plain,
    ( ~ spl3_22
    | spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f206,f189,f96,f92,f222])).

fof(f222,plain,
    ( spl3_22
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f92,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f96,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f206,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f205,f93])).

fof(f93,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

% (5623)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f205,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f204,f97])).

fof(f97,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f204,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f64,f190])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f217,plain,
    ( ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f50,f215,f212])).

fof(f215,plain,
    ( spl3_21
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f50,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f210,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f171,f141,f84,f208])).

fof(f171,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f104,f167])).

fof(f104,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f85,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f191,plain,
    ( spl3_16
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f183,f175,f141,f131,f127,f189])).

fof(f175,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f183,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f182,f149])).

fof(f149,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f142,f66])).

fof(f182,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f181,f132])).

fof(f181,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f176,f128])).

fof(f176,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f54,f175])).

fof(f54,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f173,plain,
    ( spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f167,f141,f113])).

fof(f143,plain,
    ( spl3_13
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f139,f135,f131,f127,f141])).

fof(f135,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f138,f132])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f136,f128])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f53,f135])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f108,f100,f131])).

fof(f100,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f108,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f101,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f129,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f107,f96,f127])).

fof(f107,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f97,f65])).

fof(f125,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f121,f117,f100,f96,f123])).

fof(f117,plain,
    ( spl3_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f121,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f120,f108])).

fof(f120,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f118,f107])).

fof(f118,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f52,f117])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f103,f84,f113,f110])).

fof(f103,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f85,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f58,f100])).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f57,f96])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f56,f92])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f55,f88])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f51,f84])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:34:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (5608)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (5595)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (5610)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (5602)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (5600)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (5601)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (5599)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (5597)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (5596)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (5598)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (5595)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f593,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f115,f119,f125,f129,f133,f137,f143,f173,f177,f191,f210,f217,f224,f228,f236,f261,f272,f277,f278,f288,f349,f358,f379,f398,f399,f431,f457,f475,f501,f504,f505,f539,f548,f558,f574,f590,f591,f592])).
% 0.22/0.51  fof(f592,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k1_relat_1(k2_funct_1(sK2)) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k2_struct_0(sK1) != k2_relat_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f591,plain,(
% 0.22/0.51    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(k2_funct_1(sK2)) != k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f590,plain,(
% 0.22/0.51    spl3_83 | ~spl3_55),
% 0.22/0.51    inference(avatar_split_clause,[],[f441,f429,f588])).
% 0.22/0.51  fof(f588,plain,(
% 0.22/0.51    spl3_83 <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.22/0.51  fof(f429,plain,(
% 0.22/0.51    spl3_55 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.51  fof(f441,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_55),
% 0.22/0.51    inference(resolution,[],[f430,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f430,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_55),
% 0.22/0.51    inference(avatar_component_clause,[],[f429])).
% 0.22/0.51  fof(f574,plain,(
% 0.22/0.51    spl3_81 | ~spl3_55),
% 0.22/0.51    inference(avatar_split_clause,[],[f436,f429,f572])).
% 0.22/0.51  fof(f572,plain,(
% 0.22/0.51    spl3_81 <=> k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 0.22/0.51  fof(f436,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_55),
% 0.22/0.51    inference(resolution,[],[f430,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f558,plain,(
% 0.22/0.51    spl3_77 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_60),
% 0.22/0.51    inference(avatar_split_clause,[],[f494,f473,f141,f88,f84,f556])).
% 0.22/0.51  fof(f556,plain,(
% 0.22/0.51    spl3_77 <=> k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f473,plain,(
% 0.22/0.51    spl3_60 <=> k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.22/0.51  fof(f494,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_60)),
% 0.22/0.51    inference(superposition,[],[f474,f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_13),
% 0.22/0.51    inference(subsumption_resolution,[],[f152,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2) | ~spl3_13),
% 0.22/0.51    inference(resolution,[],[f142,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f141])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(sK2) | k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f84])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) ) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f89,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f474,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~spl3_60),
% 0.22/0.51    inference(avatar_component_clause,[],[f473])).
% 0.22/0.51  fof(f548,plain,(
% 0.22/0.51    spl3_74 | ~spl3_6 | ~spl3_57 | ~spl3_58),
% 0.22/0.51    inference(avatar_split_clause,[],[f544,f459,f455,f110,f546])).
% 0.22/0.51  fof(f546,plain,(
% 0.22/0.51    spl3_74 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl3_6 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f455,plain,(
% 0.22/0.51    spl3_57 <=> v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.51  fof(f459,plain,(
% 0.22/0.51    spl3_58 <=> v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.51  fof(f544,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_6 | ~spl3_57 | ~spl3_58)),
% 0.22/0.51    inference(subsumption_resolution,[],[f543,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f110])).
% 0.22/0.51  fof(f543,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_57 | ~spl3_58)),
% 0.22/0.51    inference(subsumption_resolution,[],[f542,f456])).
% 0.22/0.51  fof(f456,plain,(
% 0.22/0.51    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_57),
% 0.22/0.51    inference(avatar_component_clause,[],[f455])).
% 0.22/0.51  fof(f542,plain,(
% 0.22/0.51    ~v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_58),
% 0.22/0.51    inference(resolution,[],[f460,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.51  fof(f460,plain,(
% 0.22/0.51    v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_58),
% 0.22/0.51    inference(avatar_component_clause,[],[f459])).
% 0.22/0.51  fof(f539,plain,(
% 0.22/0.51    ~spl3_52 | ~spl3_7 | spl3_53),
% 0.22/0.51    inference(avatar_split_clause,[],[f419,f416,f113,f413])).
% 0.22/0.51  fof(f413,plain,(
% 0.22/0.51    spl3_52 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl3_7 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f416,plain,(
% 0.22/0.51    spl3_53 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.22/0.51  fof(f419,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_7 | spl3_53)),
% 0.22/0.51    inference(subsumption_resolution,[],[f187,f417])).
% 0.22/0.51  fof(f417,plain,(
% 0.22/0.51    k1_xboole_0 != k2_relat_1(sK2) | spl3_53),
% 0.22/0.51    inference(avatar_component_clause,[],[f416])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~spl3_7),
% 0.22/0.51    inference(resolution,[],[f172,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f113])).
% 0.22/0.51  fof(f505,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relat_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_xboole_0(k1_relat_1(sK2))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f504,plain,(
% 0.22/0.51    ~spl3_49 | spl3_52),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f503])).
% 0.22/0.51  fof(f503,plain,(
% 0.22/0.51    $false | (~spl3_49 | spl3_52)),
% 0.22/0.51    inference(subsumption_resolution,[],[f502,f420])).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    k1_xboole_0 != k1_relat_1(sK2) | spl3_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f413])).
% 0.22/0.51  fof(f502,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_49),
% 0.22/0.51    inference(resolution,[],[f500,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    v1_xboole_0(k1_relat_1(sK2)) | ~spl3_49),
% 0.22/0.51    inference(avatar_component_clause,[],[f392])).
% 0.22/0.51  fof(f392,plain,(
% 0.22/0.51    spl3_49 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.51  fof(f501,plain,(
% 0.22/0.51    spl3_58 | spl3_49 | ~spl3_19 | ~spl3_50 | ~spl3_55),
% 0.22/0.51    inference(avatar_split_clause,[],[f463,f429,f396,f208,f392,f459])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl3_19 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.51  fof(f396,plain,(
% 0.22/0.51    spl3_50 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.51  fof(f463,plain,(
% 0.22/0.51    v1_xboole_0(k1_relat_1(sK2)) | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | (~spl3_19 | ~spl3_50 | ~spl3_55)),
% 0.22/0.51    inference(subsumption_resolution,[],[f462,f397])).
% 0.22/0.51  fof(f397,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_50),
% 0.22/0.51    inference(avatar_component_clause,[],[f396])).
% 0.22/0.51  fof(f462,plain,(
% 0.22/0.51    v1_xboole_0(k1_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | (~spl3_19 | ~spl3_55)),
% 0.22/0.51    inference(subsumption_resolution,[],[f442,f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl3_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f208])).
% 0.22/0.51  fof(f442,plain,(
% 0.22/0.51    v1_xboole_0(k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_55),
% 0.22/0.51    inference(resolution,[],[f430,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.51  fof(f475,plain,(
% 0.22/0.51    spl3_60 | ~spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f199,f110,f473])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) | ~spl3_6),
% 0.22/0.51    inference(resolution,[],[f111,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.51  fof(f457,plain,(
% 0.22/0.51    spl3_57 | ~spl3_55),
% 0.22/0.51    inference(avatar_split_clause,[],[f443,f429,f455])).
% 0.22/0.51  fof(f443,plain,(
% 0.22/0.51    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_55),
% 0.22/0.51    inference(resolution,[],[f430,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f431,plain,(
% 0.22/0.51    spl3_55 | ~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_33 | ~spl3_34),
% 0.22/0.51    inference(avatar_split_clause,[],[f319,f286,f283,f275,f189,f123,f88,f84,f429])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl3_9 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    spl3_16 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    spl3_31 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    spl3_33 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    spl3_34 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_33 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f318,f284])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f283])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f317,f89])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f316,f85])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f303,f296])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_9 | ~spl3_16 | ~spl3_31)),
% 0.22/0.51    inference(forward_demodulation,[],[f289,f190])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f189])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | (~spl3_9 | ~spl3_31)),
% 0.22/0.51    inference(superposition,[],[f124,f276])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_31),
% 0.22/0.51    inference(avatar_component_clause,[],[f275])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_34),
% 0.22/0.51    inference(resolution,[],[f287,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_34),
% 0.22/0.51    inference(avatar_component_clause,[],[f286])).
% 0.22/0.51  % (5615)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK1) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f398,plain,(
% 0.22/0.51    spl3_50 | ~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_33 | ~spl3_34),
% 0.22/0.51    inference(avatar_split_clause,[],[f315,f286,f283,f275,f189,f123,f88,f84,f396])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_33 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f284])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f89])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f312,f85])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f302,f296])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_34),
% 0.22/0.51    inference(resolution,[],[f287,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    spl3_45 | ~spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f184,f113,f377])).
% 0.22/0.51  fof(f377,plain,(
% 0.22/0.51    spl3_45 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_7),
% 0.22/0.51    inference(resolution,[],[f172,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    spl3_41 | ~spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f141,f123,f88,f84,f179,f356])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    spl3_41 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl3_15 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_9 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f89])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f85])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_9 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f124])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.22/0.51    inference(resolution,[],[f142,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    spl3_34 | ~spl3_7 | ~spl3_24 | ~spl3_28 | ~spl3_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f273,f270,f256,f234,f113,f286])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    spl3_24 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    spl3_28 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl3_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_24 | ~spl3_28 | ~spl3_30)),
% 0.22/0.51    inference(forward_demodulation,[],[f271,f264])).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_7 | ~spl3_24 | ~spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f263,f172])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_24 | ~spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f262,f235])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f234])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_28),
% 0.22/0.51    inference(resolution,[],[f257,f79])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f256])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f270])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k2_relat_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    spl3_31 | ~spl3_7 | ~spl3_24 | ~spl3_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f264,f256,f234,f113,f275])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    spl3_30 | ~spl3_13 | ~spl3_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f202,f189,f141,f270])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_16)),
% 0.22/0.51    inference(superposition,[],[f142,f190])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    spl3_28 | spl3_29 | ~spl3_1 | ~spl3_9 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f166,f141,f123,f84,f259,f256])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    spl3_29 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_9 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f124])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f85])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.51    inference(resolution,[],[f142,f69])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    spl3_24 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f151,f141,f234])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.51    inference(resolution,[],[f142,f81])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ~spl3_23 | ~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f220,f212,f189,f131,f127,f226])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    spl3_23 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl3_10 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    spl3_20 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_11 | ~spl3_16 | spl3_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f219,f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f131])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_10 | ~spl3_16 | spl3_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f218,f190])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_10 | spl3_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f213,f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f212])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    ~spl3_22 | spl3_3 | ~spl3_4 | ~spl3_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f206,f189,f96,f92,f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    spl3_22 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl3_3 <=> v2_struct_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl3_4 <=> l1_struct_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f205,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ~v2_struct_0(sK1) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  % (5623)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f204,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    l1_struct_0(sK1) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_16),
% 0.22/0.51    inference(superposition,[],[f64,f190])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    ~spl3_20 | ~spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f50,f215,f212])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    spl3_21 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f22])).
% 0.22/0.51  fof(f22,conjecture,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    spl3_19 | ~spl3_1 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f171,f141,f84,f208])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f167])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f85,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl3_16 | ~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f183,f175,f141,f131,f127,f189])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14)),
% 0.22/0.51    inference(forward_demodulation,[],[f182,f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_13),
% 0.22/0.51    inference(resolution,[],[f142,f66])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_10 | ~spl3_11 | ~spl3_14)),
% 0.22/0.51    inference(forward_demodulation,[],[f181,f132])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_10 | ~spl3_14)),
% 0.22/0.51    inference(forward_demodulation,[],[f176,f128])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f175])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    spl3_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f175])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl3_7 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f167,f141,f113])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl3_13 | ~spl3_10 | ~spl3_11 | ~spl3_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f139,f135,f131,f127,f141])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_10 | ~spl3_11 | ~spl3_12)),
% 0.22/0.51    inference(forward_demodulation,[],[f138,f132])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_10 | ~spl3_12)),
% 0.22/0.51    inference(forward_demodulation,[],[f136,f128])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f135])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    spl3_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f135])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl3_11 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f108,f100,f131])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl3_5 <=> l1_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.51    inference(resolution,[],[f101,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    l1_struct_0(sK0) | ~spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f100])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl3_10 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f107,f96,f127])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.22/0.51    inference(resolution,[],[f97,f65])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl3_9 | ~spl3_4 | ~spl3_5 | ~spl3_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f117,f100,f96,f123])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl3_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_8)),
% 0.22/0.51    inference(forward_demodulation,[],[f120,f108])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_8)),
% 0.22/0.51    inference(forward_demodulation,[],[f118,f107])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f117])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl3_6 | ~spl3_7 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f103,f84,f113,f110])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f85,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f58,f100])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    l1_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f96])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    l1_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f92])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f88])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f84])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (5595)------------------------------
% 0.22/0.51  % (5595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5595)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (5595)Memory used [KB]: 6524
% 0.22/0.51  % (5595)Time elapsed: 0.091 s
% 0.22/0.51  % (5595)------------------------------
% 0.22/0.51  % (5595)------------------------------
% 0.22/0.51  % (5593)Success in time 0.15 s
%------------------------------------------------------------------------------
