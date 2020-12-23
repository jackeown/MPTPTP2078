%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:48 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  290 ( 665 expanded)
%              Number of leaves         :   62 ( 289 expanded)
%              Depth                    :   16
%              Number of atoms          : 1372 (3247 expanded)
%              Number of equality atoms :  249 ( 771 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f182,f187,f193,f202,f208,f243,f266,f342,f354,f365,f406,f440,f494,f544,f560,f572,f581,f836,f845,f1073,f1346,f1386,f1428,f1501,f1557,f1579,f1594,f1596,f1597,f1598])).

fof(f1598,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1597,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK0 != k1_relat_1(sK2)
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1596,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1594,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1579,plain,
    ( ~ spl4_71
    | ~ spl4_73
    | spl4_74
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1552,f578,f541,f529,f199,f169,f1576,f1572,f1568,f1564,f1498])).

fof(f1498,plain,
    ( spl4_71
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1564,plain,
    ( spl4_73
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1568,plain,
    ( spl4_74
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1572,plain,
    ( spl4_75
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1576,plain,
    ( spl4_76
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f169,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f199,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f529,plain,
    ( spl4_38
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f541,plain,
    ( spl4_40
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f578,plain,
    ( spl4_44
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1552,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1551,f531])).

fof(f531,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f529])).

fof(f1551,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1550,f543])).

fof(f543,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f541])).

fof(f1550,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1549,f201])).

fof(f201,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1549,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1511,f171])).

fof(f171,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1511,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_44 ),
    inference(superposition,[],[f85,f580])).

fof(f580,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f578])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1557,plain,
    ( spl4_60
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1529,f578,f537,f199,f169,f1425])).

fof(f1425,plain,
    ( spl4_60
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f537,plain,
    ( spl4_39
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1529,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1528,f114])).

fof(f114,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1528,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1527,f201])).

fof(f1527,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_39
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1526,f171])).

fof(f1526,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_39
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1505,f538])).

fof(f538,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f537])).

fof(f1505,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44 ),
    inference(superposition,[],[f87,f580])).

fof(f87,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f1501,plain,
    ( spl4_71
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f1496,f557,f1498])).

fof(f557,plain,
    ( spl4_42
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1496,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1479,f117])).

fof(f117,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1479,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_42 ),
    inference(resolution,[],[f559,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f559,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f557])).

fof(f1428,plain,
    ( ~ spl4_39
    | spl4_59
    | ~ spl4_60
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_38
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f1419,f842,f529,f261,f205,f199,f184,f169,f1425,f1421,f537])).

fof(f1421,plain,
    ( spl4_59
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f184,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f205,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f261,plain,
    ( spl4_20
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f842,plain,
    ( spl4_51
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f1419,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_20
    | ~ spl4_38
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f1418,f263])).

fof(f263,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f1418,plain,
    ( sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_38
    | ~ spl4_51 ),
    inference(trivial_inequality_removal,[],[f1417])).

fof(f1417,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_38
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f1416,f531])).

fof(f1416,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1415,f201])).

fof(f1415,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1414,f171])).

fof(f1414,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1413,f207])).

fof(f207,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f1413,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1081,f186])).

fof(f186,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f1081,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_51 ),
    inference(superposition,[],[f85,f844])).

fof(f844,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f842])).

fof(f1386,plain,
    ( spl4_39
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f1385,f833,f184,f179,f174,f169,f164,f159,f154,f139,f537])).

fof(f139,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f154,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f159,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f164,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f174,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f179,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f833,plain,
    ( spl4_49
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f1385,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1384,f171])).

fof(f1384,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1383,f166])).

fof(f166,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1383,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1382,f161])).

fof(f161,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1382,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1369,f141])).

fof(f141,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1369,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1360,f101])).

fof(f101,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1360,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_49 ),
    inference(superposition,[],[f510,f835])).

fof(f835,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f833])).

fof(f510,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f509,f186])).

fof(f509,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f508,f181])).

fof(f181,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f508,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f507,f176])).

fof(f176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f507,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(superposition,[],[f97,f156])).

fof(f156,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1346,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f1345])).

fof(f1345,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_48 ),
    inference(subsumption_resolution,[],[f1344,f186])).

fof(f1344,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_48 ),
    inference(subsumption_resolution,[],[f1343,f176])).

fof(f1343,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_48 ),
    inference(subsumption_resolution,[],[f1342,f171])).

fof(f1342,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_48 ),
    inference(subsumption_resolution,[],[f1339,f161])).

fof(f1339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_48 ),
    inference(resolution,[],[f831,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f831,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f829])).

fof(f829,plain,
    ( spl4_48
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f1073,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_50 ),
    inference(avatar_contradiction_clause,[],[f1071])).

fof(f1071,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_50 ),
    inference(unit_resulting_resolution,[],[f186,f171,f176,f161,f840,f389])).

fof(f389,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f107,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f840,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl4_50
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f845,plain,
    ( ~ spl4_50
    | spl4_51
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f826,f351,f842,f838])).

fof(f351,plain,
    ( spl4_24
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f826,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_24 ),
    inference(resolution,[],[f301,f353])).

fof(f353,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f351])).

fof(f301,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f102,f116])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f836,plain,
    ( ~ spl4_48
    | spl4_49
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f825,f190,f833,f829])).

fof(f190,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f825,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f301,f192])).

fof(f192,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f581,plain,
    ( spl4_44
    | ~ spl4_39
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f576,f491,f169,f164,f159,f139,f537,f578])).

fof(f491,plain,
    ( spl4_37
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f576,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f575,f171])).

fof(f575,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f574,f166])).

fof(f574,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f573,f161])).

fof(f573,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f521,f141])).

fof(f521,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_37 ),
    inference(trivial_inequality_removal,[],[f518])).

fof(f518,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f391,f493])).

fof(f493,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f491])).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f80,f105])).

fof(f105,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f572,plain,
    ( spl4_38
    | ~ spl4_7
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f571,f491,f159,f529])).

fof(f571,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f517,f161])).

fof(f517,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_37 ),
    inference(superposition,[],[f109,f493])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f560,plain,
    ( ~ spl4_39
    | spl4_42
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f555,f491,f169,f164,f159,f557,f537])).

fof(f555,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f554,f171])).

fof(f554,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f553,f166])).

fof(f553,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f524,f161])).

fof(f524,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_37 ),
    inference(trivial_inequality_removal,[],[f514])).

fof(f514,plain,
    ( sK0 != sK0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f84,f493])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f544,plain,
    ( ~ spl4_39
    | spl4_40
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f535,f491,f169,f164,f159,f541,f537])).

fof(f535,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f534,f171])).

fof(f534,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f533,f166])).

fof(f533,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f526,f161])).

fof(f526,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_37 ),
    inference(trivial_inequality_removal,[],[f512])).

fof(f512,plain,
    ( sK0 != sK0
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f82,f493])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f494,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f489,f190,f184,f179,f174,f169,f164,f159,f491])).

fof(f489,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f488,f171])).

fof(f488,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f487,f166])).

fof(f487,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f486,f161])).

fof(f486,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f485,f186])).

fof(f485,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f484,f181])).

fof(f484,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f481,f176])).

fof(f481,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f480,f192])).

fof(f480,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f104,f105])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f440,plain,
    ( spl4_31
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f439,f403,f205,f184,f144,f432])).

fof(f432,plain,
    ( spl4_31
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f144,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f403,plain,
    ( spl4_29
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f439,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f438,f113])).

fof(f113,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f438,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f437,f207])).

fof(f437,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f436,f186])).

fof(f436,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f424,f146])).

fof(f146,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f424,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_29 ),
    inference(superposition,[],[f86,f405])).

fof(f405,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f403])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f406,plain,
    ( spl4_29
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f401,f184,f179,f174,f154,f144,f134,f403])).

fof(f134,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f401,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f400,f186])).

fof(f400,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f399,f181])).

fof(f399,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f398,f176])).

fof(f398,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f397,f146])).

fof(f397,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f396,f136])).

fof(f136,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f396,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f391,f156])).

fof(f365,plain,
    ( ~ spl4_25
    | spl4_1
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f360,f339,f159,f129,f362])).

fof(f362,plain,
    ( spl4_25
  <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f129,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f339,plain,
    ( spl4_23
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f360,plain,
    ( ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | spl4_1
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f355,f131])).

fof(f131,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f355,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(resolution,[],[f341,f299])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | sK3 = X0
        | ~ r2_relset_1(sK1,sK0,X0,sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f102,f161])).

fof(f341,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f339])).

fof(f354,plain,
    ( spl4_24
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f349,f190,f184,f174,f169,f159,f351])).

fof(f349,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f348,f186])).

fof(f348,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f347,f176])).

fof(f347,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f346,f171])).

fof(f346,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f343,f161])).

fof(f343,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f192,f108])).

fof(f342,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f337,f184,f179,f174,f154,f144,f339])).

fof(f337,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f336,f186])).

fof(f336,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f335,f181])).

fof(f335,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f334,f176])).

fof(f334,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f333,f146])).

fof(f333,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f84,f156])).

fof(f266,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f265,f174,f154,f261])).

fof(f265,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f258,f176])).

fof(f258,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f156,f109])).

fof(f243,plain,
    ( spl4_18
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f236,f159,f240])).

fof(f240,plain,
    ( spl4_18
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f236,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f127,f161])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f208,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f203,f174,f205])).

fof(f203,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f195,f117])).

fof(f195,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f115,f176])).

fof(f202,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f197,f159,f199])).

fof(f197,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f194,f117])).

fof(f194,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f115,f161])).

fof(f193,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f188,f149,f190])).

fof(f149,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f188,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f151,f105])).

fof(f151,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f187,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f68,f184])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f62,f61])).

fof(f61,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f182,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f69,f179])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f177,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f70,f174])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f172,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f71,f169])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f167,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f72,f164])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f162,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f73,f159])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f157,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f74,f154])).

fof(f74,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f152,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f75,f149])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f147,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f76,f144])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f142,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f77,f139])).

fof(f77,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f63])).

fof(f137,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f78,f134])).

fof(f78,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

fof(f132,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f79,f129])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (11551)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (11539)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (11548)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (11561)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (11553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (11547)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (11540)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (11537)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (11533)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (11552)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (11541)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (11542)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (11555)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (11559)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (11562)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (11543)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (11560)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (11554)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (11535)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (11556)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (11550)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (11546)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (11538)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (11544)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (11549)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (11534)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (11545)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (11557)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.56  % (11558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.56  % (11536)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.46/0.56  % (11549)Refutation not found, incomplete strategy% (11549)------------------------------
% 1.46/0.56  % (11549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (11549)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (11549)Memory used [KB]: 10746
% 1.46/0.57  % (11549)Time elapsed: 0.126 s
% 1.46/0.57  % (11549)------------------------------
% 1.46/0.57  % (11549)------------------------------
% 1.92/0.63  % (11554)Refutation found. Thanks to Tanya!
% 1.92/0.63  % SZS status Theorem for theBenchmark
% 1.92/0.63  % SZS output start Proof for theBenchmark
% 1.92/0.63  fof(f1599,plain,(
% 1.92/0.63    $false),
% 1.92/0.63    inference(avatar_sat_refutation,[],[f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f182,f187,f193,f202,f208,f243,f266,f342,f354,f365,f406,f440,f494,f544,f560,f572,f581,f836,f845,f1073,f1346,f1386,f1428,f1501,f1557,f1579,f1594,f1596,f1597,f1598])).
% 1.92/0.63  fof(f1598,plain,(
% 1.92/0.63    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | ~r2_relset_1(sK1,sK0,sK3,sK3)),
% 1.92/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.92/0.63  fof(f1597,plain,(
% 1.92/0.63    sK2 != k2_funct_1(sK3) | sK0 != k1_relat_1(sK2) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.92/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.92/0.63  fof(f1596,plain,(
% 1.92/0.63    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.92/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.92/0.63  fof(f1594,plain,(
% 1.92/0.63    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.92/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.92/0.63  fof(f1579,plain,(
% 1.92/0.63    ~spl4_71 | ~spl4_73 | spl4_74 | ~spl4_75 | ~spl4_76 | ~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_40 | ~spl4_44),
% 1.92/0.63    inference(avatar_split_clause,[],[f1552,f578,f541,f529,f199,f169,f1576,f1572,f1568,f1564,f1498])).
% 1.92/0.63  fof(f1498,plain,(
% 1.92/0.63    spl4_71 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.92/0.63  fof(f1564,plain,(
% 1.92/0.63    spl4_73 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.92/0.63  fof(f1568,plain,(
% 1.92/0.63    spl4_74 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 1.92/0.63  fof(f1572,plain,(
% 1.92/0.63    spl4_75 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.92/0.63  fof(f1576,plain,(
% 1.92/0.63    spl4_76 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 1.92/0.63  fof(f169,plain,(
% 1.92/0.63    spl4_9 <=> v1_funct_1(sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.92/0.63  fof(f199,plain,(
% 1.92/0.63    spl4_14 <=> v1_relat_1(sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.92/0.63  fof(f529,plain,(
% 1.92/0.63    spl4_38 <=> sK0 = k2_relat_1(sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.92/0.63  fof(f541,plain,(
% 1.92/0.63    spl4_40 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.92/0.63  fof(f578,plain,(
% 1.92/0.63    spl4_44 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.92/0.63  fof(f1552,plain,(
% 1.92/0.63    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_40 | ~spl4_44)),
% 1.92/0.63    inference(forward_demodulation,[],[f1551,f531])).
% 1.92/0.63  fof(f531,plain,(
% 1.92/0.63    sK0 = k2_relat_1(sK3) | ~spl4_38),
% 1.92/0.63    inference(avatar_component_clause,[],[f529])).
% 1.92/0.63  fof(f1551,plain,(
% 1.92/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_40 | ~spl4_44)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1550,f543])).
% 1.92/0.63  fof(f543,plain,(
% 1.92/0.63    v1_funct_1(k2_funct_1(sK3)) | ~spl4_40),
% 1.92/0.63    inference(avatar_component_clause,[],[f541])).
% 1.92/0.63  fof(f1550,plain,(
% 1.92/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_44)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1549,f201])).
% 1.92/0.63  fof(f201,plain,(
% 1.92/0.63    v1_relat_1(sK3) | ~spl4_14),
% 1.92/0.63    inference(avatar_component_clause,[],[f199])).
% 1.92/0.63  fof(f1549,plain,(
% 1.92/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_44)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1511,f171])).
% 1.92/0.63  fof(f171,plain,(
% 1.92/0.63    v1_funct_1(sK3) | ~spl4_9),
% 1.92/0.63    inference(avatar_component_clause,[],[f169])).
% 1.92/0.63  fof(f1511,plain,(
% 1.92/0.63    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_44),
% 1.92/0.63    inference(superposition,[],[f85,f580])).
% 1.92/0.63  fof(f580,plain,(
% 1.92/0.63    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_44),
% 1.92/0.63    inference(avatar_component_clause,[],[f578])).
% 1.92/0.63  fof(f85,plain,(
% 1.92/0.63    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f35])).
% 1.92/0.63  fof(f35,plain,(
% 1.92/0.63    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.92/0.63    inference(flattening,[],[f34])).
% 1.92/0.63  fof(f34,plain,(
% 1.92/0.63    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.92/0.63    inference(ennf_transformation,[],[f13])).
% 1.92/0.63  fof(f13,axiom,(
% 1.92/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.92/0.63  fof(f1557,plain,(
% 1.92/0.63    spl4_60 | ~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_44),
% 1.92/0.63    inference(avatar_split_clause,[],[f1529,f578,f537,f199,f169,f1425])).
% 1.92/0.63  fof(f1425,plain,(
% 1.92/0.63    spl4_60 <=> sK1 = k1_relat_1(sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.92/0.63  fof(f537,plain,(
% 1.92/0.63    spl4_39 <=> v2_funct_1(sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.92/0.63  fof(f1529,plain,(
% 1.92/0.63    sK1 = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_44)),
% 1.92/0.63    inference(forward_demodulation,[],[f1528,f114])).
% 1.92/0.63  fof(f114,plain,(
% 1.92/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.92/0.63    inference(cnf_transformation,[],[f6])).
% 1.92/0.63  fof(f6,axiom,(
% 1.92/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.92/0.63  fof(f1528,plain,(
% 1.92/0.63    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | (~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_44)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1527,f201])).
% 1.92/0.63  fof(f1527,plain,(
% 1.92/0.63    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_39 | ~spl4_44)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1526,f171])).
% 1.92/0.63  fof(f1526,plain,(
% 1.92/0.63    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_39 | ~spl4_44)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1505,f538])).
% 1.92/0.63  fof(f538,plain,(
% 1.92/0.63    v2_funct_1(sK3) | ~spl4_39),
% 1.92/0.63    inference(avatar_component_clause,[],[f537])).
% 1.92/0.63  fof(f1505,plain,(
% 1.92/0.63    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_44),
% 1.92/0.63    inference(superposition,[],[f87,f580])).
% 1.92/0.63  fof(f87,plain,(
% 1.92/0.63    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f37])).
% 1.92/0.63  fof(f37,plain,(
% 1.92/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.92/0.63    inference(flattening,[],[f36])).
% 1.92/0.63  fof(f36,plain,(
% 1.92/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.92/0.63    inference(ennf_transformation,[],[f12])).
% 1.92/0.63  fof(f12,axiom,(
% 1.92/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.92/0.63  fof(f1501,plain,(
% 1.92/0.63    spl4_71 | ~spl4_42),
% 1.92/0.63    inference(avatar_split_clause,[],[f1496,f557,f1498])).
% 1.92/0.63  fof(f557,plain,(
% 1.92/0.63    spl4_42 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.92/0.63  fof(f1496,plain,(
% 1.92/0.63    v1_relat_1(k2_funct_1(sK3)) | ~spl4_42),
% 1.92/0.63    inference(subsumption_resolution,[],[f1479,f117])).
% 1.92/0.63  fof(f117,plain,(
% 1.92/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.92/0.63    inference(cnf_transformation,[],[f4])).
% 1.92/0.63  fof(f4,axiom,(
% 1.92/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.92/0.63  fof(f1479,plain,(
% 1.92/0.63    v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_42),
% 1.92/0.63    inference(resolution,[],[f559,f115])).
% 1.92/0.63  fof(f115,plain,(
% 1.92/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f57])).
% 1.92/0.63  fof(f57,plain,(
% 1.92/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.92/0.63    inference(ennf_transformation,[],[f2])).
% 1.92/0.63  fof(f2,axiom,(
% 1.92/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.92/0.63  fof(f559,plain,(
% 1.92/0.63    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_42),
% 1.92/0.63    inference(avatar_component_clause,[],[f557])).
% 1.92/0.63  fof(f1428,plain,(
% 1.92/0.63    ~spl4_39 | spl4_59 | ~spl4_60 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_20 | ~spl4_38 | ~spl4_51),
% 1.92/0.63    inference(avatar_split_clause,[],[f1419,f842,f529,f261,f205,f199,f184,f169,f1425,f1421,f537])).
% 1.92/0.63  fof(f1421,plain,(
% 1.92/0.63    spl4_59 <=> sK2 = k2_funct_1(sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.92/0.63  fof(f184,plain,(
% 1.92/0.63    spl4_12 <=> v1_funct_1(sK2)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.92/0.63  fof(f205,plain,(
% 1.92/0.63    spl4_15 <=> v1_relat_1(sK2)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.92/0.63  fof(f261,plain,(
% 1.92/0.63    spl4_20 <=> sK1 = k2_relat_1(sK2)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.92/0.63  fof(f842,plain,(
% 1.92/0.63    spl4_51 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.92/0.63  fof(f1419,plain,(
% 1.92/0.63    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_20 | ~spl4_38 | ~spl4_51)),
% 1.92/0.63    inference(forward_demodulation,[],[f1418,f263])).
% 1.92/0.63  fof(f263,plain,(
% 1.92/0.63    sK1 = k2_relat_1(sK2) | ~spl4_20),
% 1.92/0.63    inference(avatar_component_clause,[],[f261])).
% 1.92/0.63  fof(f1418,plain,(
% 1.92/0.63    sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_38 | ~spl4_51)),
% 1.92/0.63    inference(trivial_inequality_removal,[],[f1417])).
% 1.92/0.63  fof(f1417,plain,(
% 1.92/0.63    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_38 | ~spl4_51)),
% 1.92/0.63    inference(forward_demodulation,[],[f1416,f531])).
% 1.92/0.63  fof(f1416,plain,(
% 1.92/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_51)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1415,f201])).
% 1.92/0.63  fof(f1415,plain,(
% 1.92/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_51)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1414,f171])).
% 1.92/0.63  fof(f1414,plain,(
% 1.92/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_51)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1413,f207])).
% 1.92/0.63  fof(f207,plain,(
% 1.92/0.63    v1_relat_1(sK2) | ~spl4_15),
% 1.92/0.63    inference(avatar_component_clause,[],[f205])).
% 1.92/0.63  fof(f1413,plain,(
% 1.92/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_51)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1081,f186])).
% 1.92/0.63  fof(f186,plain,(
% 1.92/0.63    v1_funct_1(sK2) | ~spl4_12),
% 1.92/0.63    inference(avatar_component_clause,[],[f184])).
% 1.92/0.63  fof(f1081,plain,(
% 1.92/0.63    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_51),
% 1.92/0.63    inference(superposition,[],[f85,f844])).
% 1.92/0.63  fof(f844,plain,(
% 1.92/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_51),
% 1.92/0.63    inference(avatar_component_clause,[],[f842])).
% 1.92/0.63  fof(f1386,plain,(
% 1.92/0.63    spl4_39 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49),
% 1.92/0.63    inference(avatar_split_clause,[],[f1385,f833,f184,f179,f174,f169,f164,f159,f154,f139,f537])).
% 1.92/0.63  fof(f139,plain,(
% 1.92/0.63    spl4_3 <=> k1_xboole_0 = sK0),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.92/0.63  fof(f154,plain,(
% 1.92/0.63    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.92/0.63  fof(f159,plain,(
% 1.92/0.63    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.92/0.63  fof(f164,plain,(
% 1.92/0.63    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.92/0.63  fof(f174,plain,(
% 1.92/0.63    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.92/0.63  fof(f179,plain,(
% 1.92/0.63    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.92/0.63  fof(f833,plain,(
% 1.92/0.63    spl4_49 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.92/0.63  fof(f1385,plain,(
% 1.92/0.63    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1384,f171])).
% 1.92/0.63  fof(f1384,plain,(
% 1.92/0.63    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1383,f166])).
% 1.92/0.63  fof(f166,plain,(
% 1.92/0.63    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.92/0.63    inference(avatar_component_clause,[],[f164])).
% 1.92/0.63  fof(f1383,plain,(
% 1.92/0.63    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1382,f161])).
% 1.92/0.63  fof(f161,plain,(
% 1.92/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.92/0.63    inference(avatar_component_clause,[],[f159])).
% 1.92/0.63  fof(f1382,plain,(
% 1.92/0.63    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1369,f141])).
% 1.92/0.63  fof(f141,plain,(
% 1.92/0.63    k1_xboole_0 != sK0 | spl4_3),
% 1.92/0.63    inference(avatar_component_clause,[],[f139])).
% 1.92/0.63  fof(f1369,plain,(
% 1.92/0.63    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1360,f101])).
% 1.92/0.63  fof(f101,plain,(
% 1.92/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.92/0.63    inference(cnf_transformation,[],[f10])).
% 1.92/0.63  fof(f10,axiom,(
% 1.92/0.63    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.92/0.63  fof(f1360,plain,(
% 1.92/0.63    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_49)),
% 1.92/0.63    inference(superposition,[],[f510,f835])).
% 1.92/0.63  fof(f835,plain,(
% 1.92/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_49),
% 1.92/0.63    inference(avatar_component_clause,[],[f833])).
% 1.92/0.63  fof(f510,plain,(
% 1.92/0.63    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.92/0.63    inference(subsumption_resolution,[],[f509,f186])).
% 1.92/0.63  fof(f509,plain,(
% 1.92/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.92/0.63    inference(subsumption_resolution,[],[f508,f181])).
% 1.92/0.63  fof(f181,plain,(
% 1.92/0.63    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.92/0.63    inference(avatar_component_clause,[],[f179])).
% 1.92/0.63  fof(f508,plain,(
% 1.92/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.92/0.63    inference(subsumption_resolution,[],[f507,f176])).
% 1.92/0.63  fof(f176,plain,(
% 1.92/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.92/0.63    inference(avatar_component_clause,[],[f174])).
% 1.92/0.63  fof(f507,plain,(
% 1.92/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.92/0.63    inference(trivial_inequality_removal,[],[f504])).
% 1.92/0.63  fof(f504,plain,(
% 1.92/0.63    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.92/0.63    inference(superposition,[],[f97,f156])).
% 1.92/0.63  fof(f156,plain,(
% 1.92/0.63    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.92/0.63    inference(avatar_component_clause,[],[f154])).
% 1.92/0.63  fof(f97,plain,(
% 1.92/0.63    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f45])).
% 1.92/0.63  fof(f45,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.92/0.63    inference(flattening,[],[f44])).
% 1.92/0.63  fof(f44,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.92/0.63    inference(ennf_transformation,[],[f22])).
% 1.92/0.63  fof(f22,axiom,(
% 1.92/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.92/0.63  fof(f1346,plain,(
% 1.92/0.63    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_48),
% 1.92/0.63    inference(avatar_contradiction_clause,[],[f1345])).
% 1.92/0.63  fof(f1345,plain,(
% 1.92/0.63    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_48)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1344,f186])).
% 1.92/0.63  fof(f1344,plain,(
% 1.92/0.63    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_48)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1343,f176])).
% 1.92/0.63  fof(f1343,plain,(
% 1.92/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_48)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1342,f171])).
% 1.92/0.63  fof(f1342,plain,(
% 1.92/0.63    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_48)),
% 1.92/0.63    inference(subsumption_resolution,[],[f1339,f161])).
% 1.92/0.63  fof(f1339,plain,(
% 1.92/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_48),
% 1.92/0.63    inference(resolution,[],[f831,f107])).
% 1.92/0.63  fof(f107,plain,(
% 1.92/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f53])).
% 1.92/0.63  fof(f53,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.92/0.63    inference(flattening,[],[f52])).
% 1.92/0.63  fof(f52,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.92/0.63    inference(ennf_transformation,[],[f18])).
% 1.92/0.63  fof(f18,axiom,(
% 1.92/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.92/0.63  fof(f831,plain,(
% 1.92/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_48),
% 1.92/0.63    inference(avatar_component_clause,[],[f829])).
% 1.92/0.63  fof(f829,plain,(
% 1.92/0.63    spl4_48 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.92/0.63  fof(f1073,plain,(
% 1.92/0.63    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_50),
% 1.92/0.63    inference(avatar_contradiction_clause,[],[f1071])).
% 1.92/0.63  fof(f1071,plain,(
% 1.92/0.63    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_50)),
% 1.92/0.63    inference(unit_resulting_resolution,[],[f186,f171,f176,f161,f840,f389])).
% 1.92/0.63  fof(f389,plain,(
% 1.92/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.92/0.63    inference(duplicate_literal_removal,[],[f388])).
% 1.92/0.63  fof(f388,plain,(
% 1.92/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.92/0.63    inference(superposition,[],[f107,f108])).
% 1.92/0.63  fof(f108,plain,(
% 1.92/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f55])).
% 1.92/0.63  fof(f55,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.92/0.63    inference(flattening,[],[f54])).
% 1.92/0.63  fof(f54,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.92/0.63    inference(ennf_transformation,[],[f19])).
% 1.92/0.63  fof(f19,axiom,(
% 1.92/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.92/0.63  fof(f840,plain,(
% 1.92/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_50),
% 1.92/0.63    inference(avatar_component_clause,[],[f838])).
% 1.92/0.63  fof(f838,plain,(
% 1.92/0.63    spl4_50 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.92/0.63  fof(f845,plain,(
% 1.92/0.63    ~spl4_50 | spl4_51 | ~spl4_24),
% 1.92/0.63    inference(avatar_split_clause,[],[f826,f351,f842,f838])).
% 1.92/0.63  fof(f351,plain,(
% 1.92/0.63    spl4_24 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.92/0.63  fof(f826,plain,(
% 1.92/0.63    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_24),
% 1.92/0.63    inference(resolution,[],[f301,f353])).
% 1.92/0.63  fof(f353,plain,(
% 1.92/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_24),
% 1.92/0.63    inference(avatar_component_clause,[],[f351])).
% 1.92/0.63  fof(f301,plain,(
% 1.92/0.63    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.92/0.63    inference(resolution,[],[f102,f116])).
% 1.92/0.63  fof(f116,plain,(
% 1.92/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.92/0.63    inference(cnf_transformation,[],[f17])).
% 1.92/0.63  fof(f17,axiom,(
% 1.92/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.92/0.63  fof(f102,plain,(
% 1.92/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.92/0.63    inference(cnf_transformation,[],[f64])).
% 1.92/0.63  fof(f64,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.63    inference(nnf_transformation,[],[f49])).
% 1.92/0.63  fof(f49,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.63    inference(flattening,[],[f48])).
% 1.92/0.63  fof(f48,plain,(
% 1.92/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.92/0.63    inference(ennf_transformation,[],[f16])).
% 1.92/0.63  fof(f16,axiom,(
% 1.92/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.92/0.63  fof(f836,plain,(
% 1.92/0.63    ~spl4_48 | spl4_49 | ~spl4_13),
% 1.92/0.63    inference(avatar_split_clause,[],[f825,f190,f833,f829])).
% 1.92/0.63  fof(f190,plain,(
% 1.92/0.63    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.92/0.63  fof(f825,plain,(
% 1.92/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.92/0.63    inference(resolution,[],[f301,f192])).
% 1.92/0.63  fof(f192,plain,(
% 1.92/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.92/0.63    inference(avatar_component_clause,[],[f190])).
% 1.92/0.63  fof(f581,plain,(
% 1.92/0.63    spl4_44 | ~spl4_39 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_37),
% 1.92/0.63    inference(avatar_split_clause,[],[f576,f491,f169,f164,f159,f139,f537,f578])).
% 1.92/0.63  fof(f491,plain,(
% 1.92/0.63    spl4_37 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.92/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.92/0.63  fof(f576,plain,(
% 1.92/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f575,f171])).
% 1.92/0.63  fof(f575,plain,(
% 1.92/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f574,f166])).
% 1.92/0.63  fof(f574,plain,(
% 1.92/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f573,f161])).
% 1.92/0.63  fof(f573,plain,(
% 1.92/0.63    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f521,f141])).
% 1.92/0.63  fof(f521,plain,(
% 1.92/0.63    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_37),
% 1.92/0.63    inference(trivial_inequality_removal,[],[f518])).
% 1.92/0.63  fof(f518,plain,(
% 1.92/0.63    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_37),
% 1.92/0.63    inference(superposition,[],[f391,f493])).
% 1.92/0.63  fof(f493,plain,(
% 1.92/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_37),
% 1.92/0.63    inference(avatar_component_clause,[],[f491])).
% 1.92/0.63  fof(f391,plain,(
% 1.92/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.92/0.63    inference(forward_demodulation,[],[f80,f105])).
% 1.92/0.63  fof(f105,plain,(
% 1.92/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f20])).
% 1.92/0.63  fof(f20,axiom,(
% 1.92/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.92/0.63  fof(f80,plain,(
% 1.92/0.63    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f31])).
% 1.92/0.63  fof(f31,plain,(
% 1.92/0.63    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.92/0.63    inference(flattening,[],[f30])).
% 1.92/0.63  fof(f30,plain,(
% 1.92/0.63    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.92/0.63    inference(ennf_transformation,[],[f24])).
% 1.92/0.63  fof(f24,axiom,(
% 1.92/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.92/0.63  fof(f572,plain,(
% 1.92/0.63    spl4_38 | ~spl4_7 | ~spl4_37),
% 1.92/0.63    inference(avatar_split_clause,[],[f571,f491,f159,f529])).
% 1.92/0.63  fof(f571,plain,(
% 1.92/0.63    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f517,f161])).
% 1.92/0.63  fof(f517,plain,(
% 1.92/0.63    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_37),
% 1.92/0.63    inference(superposition,[],[f109,f493])).
% 1.92/0.63  fof(f109,plain,(
% 1.92/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.92/0.63    inference(cnf_transformation,[],[f56])).
% 1.92/0.63  fof(f56,plain,(
% 1.92/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.92/0.63    inference(ennf_transformation,[],[f15])).
% 1.92/0.63  fof(f15,axiom,(
% 1.92/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.92/0.63  fof(f560,plain,(
% 1.92/0.63    ~spl4_39 | spl4_42 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_37),
% 1.92/0.63    inference(avatar_split_clause,[],[f555,f491,f169,f164,f159,f557,f537])).
% 1.92/0.63  fof(f555,plain,(
% 1.92/0.63    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f554,f171])).
% 1.92/0.63  fof(f554,plain,(
% 1.92/0.63    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f553,f166])).
% 1.92/0.63  fof(f553,plain,(
% 1.92/0.63    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_37)),
% 1.92/0.63    inference(subsumption_resolution,[],[f524,f161])).
% 1.92/0.63  fof(f524,plain,(
% 1.92/0.63    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_37),
% 1.92/0.63    inference(trivial_inequality_removal,[],[f514])).
% 1.92/0.63  fof(f514,plain,(
% 1.92/0.63    sK0 != sK0 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_37),
% 1.92/0.63    inference(superposition,[],[f84,f493])).
% 1.92/0.63  fof(f84,plain,(
% 1.92/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.92/0.63    inference(cnf_transformation,[],[f33])).
% 1.92/0.63  fof(f33,plain,(
% 1.92/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.92/0.63    inference(flattening,[],[f32])).
% 1.92/0.63  fof(f32,plain,(
% 1.92/0.63    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.92/0.63    inference(ennf_transformation,[],[f23])).
% 1.92/0.63  fof(f23,axiom,(
% 1.92/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.92/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.10/0.65  fof(f544,plain,(
% 2.10/0.65    ~spl4_39 | spl4_40 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_37),
% 2.10/0.65    inference(avatar_split_clause,[],[f535,f491,f169,f164,f159,f541,f537])).
% 2.10/0.65  fof(f535,plain,(
% 2.10/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_37)),
% 2.10/0.65    inference(subsumption_resolution,[],[f534,f171])).
% 2.10/0.65  fof(f534,plain,(
% 2.10/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_37)),
% 2.10/0.65    inference(subsumption_resolution,[],[f533,f166])).
% 2.10/0.65  fof(f533,plain,(
% 2.10/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_37)),
% 2.10/0.65    inference(subsumption_resolution,[],[f526,f161])).
% 2.10/0.65  fof(f526,plain,(
% 2.10/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_37),
% 2.10/0.65    inference(trivial_inequality_removal,[],[f512])).
% 2.10/0.65  fof(f512,plain,(
% 2.10/0.65    sK0 != sK0 | v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_37),
% 2.10/0.65    inference(superposition,[],[f82,f493])).
% 2.10/0.65  fof(f82,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f33])).
% 2.10/0.65  fof(f494,plain,(
% 2.10/0.65    spl4_37 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 2.10/0.65    inference(avatar_split_clause,[],[f489,f190,f184,f179,f174,f169,f164,f159,f491])).
% 2.10/0.65  fof(f489,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f488,f171])).
% 2.10/0.65  fof(f488,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f487,f166])).
% 2.10/0.65  fof(f487,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f486,f161])).
% 2.10/0.65  fof(f486,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f485,f186])).
% 2.10/0.65  fof(f485,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f484,f181])).
% 2.10/0.65  fof(f484,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f481,f176])).
% 2.10/0.65  fof(f481,plain,(
% 2.10/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 2.10/0.65    inference(resolution,[],[f480,f192])).
% 2.10/0.65  fof(f480,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.65    inference(forward_demodulation,[],[f104,f105])).
% 2.10/0.65  fof(f104,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f51])).
% 2.10/0.65  fof(f51,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.10/0.65    inference(flattening,[],[f50])).
% 2.10/0.65  fof(f50,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.10/0.65    inference(ennf_transformation,[],[f21])).
% 2.10/0.65  fof(f21,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.10/0.65  fof(f440,plain,(
% 2.10/0.65    spl4_31 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_29),
% 2.10/0.65    inference(avatar_split_clause,[],[f439,f403,f205,f184,f144,f432])).
% 2.10/0.65  fof(f432,plain,(
% 2.10/0.65    spl4_31 <=> sK0 = k1_relat_1(sK2)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.10/0.65  fof(f144,plain,(
% 2.10/0.65    spl4_4 <=> v2_funct_1(sK2)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.10/0.65  fof(f403,plain,(
% 2.10/0.65    spl4_29 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.10/0.65  fof(f439,plain,(
% 2.10/0.65    sK0 = k1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_29)),
% 2.10/0.65    inference(forward_demodulation,[],[f438,f113])).
% 2.10/0.65  fof(f113,plain,(
% 2.10/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.10/0.65    inference(cnf_transformation,[],[f6])).
% 2.10/0.65  fof(f438,plain,(
% 2.10/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_29)),
% 2.10/0.65    inference(subsumption_resolution,[],[f437,f207])).
% 2.10/0.65  fof(f437,plain,(
% 2.10/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_29)),
% 2.10/0.65    inference(subsumption_resolution,[],[f436,f186])).
% 2.10/0.65  fof(f436,plain,(
% 2.10/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_29)),
% 2.10/0.65    inference(subsumption_resolution,[],[f424,f146])).
% 2.10/0.65  fof(f146,plain,(
% 2.10/0.65    v2_funct_1(sK2) | ~spl4_4),
% 2.10/0.65    inference(avatar_component_clause,[],[f144])).
% 2.10/0.65  fof(f424,plain,(
% 2.10/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_29),
% 2.10/0.65    inference(superposition,[],[f86,f405])).
% 2.10/0.65  fof(f405,plain,(
% 2.10/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_29),
% 2.10/0.65    inference(avatar_component_clause,[],[f403])).
% 2.10/0.65  fof(f86,plain,(
% 2.10/0.65    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f37])).
% 2.10/0.65  fof(f406,plain,(
% 2.10/0.65    spl4_29 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.10/0.65    inference(avatar_split_clause,[],[f401,f184,f179,f174,f154,f144,f134,f403])).
% 2.10/0.65  fof(f134,plain,(
% 2.10/0.65    spl4_2 <=> k1_xboole_0 = sK1),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.10/0.65  fof(f401,plain,(
% 2.10/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.10/0.65    inference(subsumption_resolution,[],[f400,f186])).
% 2.10/0.65  fof(f400,plain,(
% 2.10/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.10/0.65    inference(subsumption_resolution,[],[f399,f181])).
% 2.10/0.65  fof(f399,plain,(
% 2.10/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.10/0.65    inference(subsumption_resolution,[],[f398,f176])).
% 2.10/0.65  fof(f398,plain,(
% 2.10/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.10/0.65    inference(subsumption_resolution,[],[f397,f146])).
% 2.10/0.65  fof(f397,plain,(
% 2.10/0.65    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.10/0.65    inference(subsumption_resolution,[],[f396,f136])).
% 2.10/0.65  fof(f136,plain,(
% 2.10/0.65    k1_xboole_0 != sK1 | spl4_2),
% 2.10/0.65    inference(avatar_component_clause,[],[f134])).
% 2.10/0.65  fof(f396,plain,(
% 2.10/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.10/0.65    inference(trivial_inequality_removal,[],[f393])).
% 2.10/0.65  fof(f393,plain,(
% 2.10/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.10/0.65    inference(superposition,[],[f391,f156])).
% 2.10/0.65  fof(f365,plain,(
% 2.10/0.65    ~spl4_25 | spl4_1 | ~spl4_7 | ~spl4_23),
% 2.10/0.65    inference(avatar_split_clause,[],[f360,f339,f159,f129,f362])).
% 2.10/0.65  fof(f362,plain,(
% 2.10/0.65    spl4_25 <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.10/0.65  fof(f129,plain,(
% 2.10/0.65    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.10/0.65  fof(f339,plain,(
% 2.10/0.65    spl4_23 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.10/0.65  fof(f360,plain,(
% 2.10/0.65    ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | (spl4_1 | ~spl4_7 | ~spl4_23)),
% 2.10/0.65    inference(subsumption_resolution,[],[f355,f131])).
% 2.10/0.65  fof(f131,plain,(
% 2.10/0.65    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.10/0.65    inference(avatar_component_clause,[],[f129])).
% 2.10/0.65  fof(f355,plain,(
% 2.10/0.65    k2_funct_1(sK2) = sK3 | ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | (~spl4_7 | ~spl4_23)),
% 2.10/0.65    inference(resolution,[],[f341,f299])).
% 2.10/0.65  fof(f299,plain,(
% 2.10/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK3 = X0 | ~r2_relset_1(sK1,sK0,X0,sK3)) ) | ~spl4_7),
% 2.10/0.65    inference(resolution,[],[f102,f161])).
% 2.10/0.65  fof(f341,plain,(
% 2.10/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_23),
% 2.10/0.65    inference(avatar_component_clause,[],[f339])).
% 2.10/0.65  fof(f354,plain,(
% 2.10/0.65    spl4_24 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.10/0.65    inference(avatar_split_clause,[],[f349,f190,f184,f174,f169,f159,f351])).
% 2.10/0.65  fof(f349,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f348,f186])).
% 2.10/0.65  fof(f348,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f347,f176])).
% 2.10/0.65  fof(f347,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f346,f171])).
% 2.10/0.65  fof(f346,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.10/0.65    inference(subsumption_resolution,[],[f343,f161])).
% 2.10/0.65  fof(f343,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.10/0.65    inference(superposition,[],[f192,f108])).
% 2.10/0.65  fof(f342,plain,(
% 2.10/0.65    spl4_23 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.10/0.65    inference(avatar_split_clause,[],[f337,f184,f179,f174,f154,f144,f339])).
% 2.10/0.65  fof(f337,plain,(
% 2.10/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.10/0.65    inference(subsumption_resolution,[],[f336,f186])).
% 2.10/0.65  fof(f336,plain,(
% 2.10/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.10/0.65    inference(subsumption_resolution,[],[f335,f181])).
% 2.10/0.65  fof(f335,plain,(
% 2.10/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.10/0.65    inference(subsumption_resolution,[],[f334,f176])).
% 2.10/0.65  fof(f334,plain,(
% 2.10/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 2.10/0.65    inference(subsumption_resolution,[],[f333,f146])).
% 2.10/0.65  fof(f333,plain,(
% 2.10/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.10/0.65    inference(trivial_inequality_removal,[],[f330])).
% 2.10/0.65  fof(f330,plain,(
% 2.10/0.65    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.10/0.65    inference(superposition,[],[f84,f156])).
% 2.10/0.65  fof(f266,plain,(
% 2.10/0.65    spl4_20 | ~spl4_6 | ~spl4_10),
% 2.10/0.65    inference(avatar_split_clause,[],[f265,f174,f154,f261])).
% 2.10/0.65  fof(f265,plain,(
% 2.10/0.65    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 2.10/0.65    inference(subsumption_resolution,[],[f258,f176])).
% 2.10/0.65  fof(f258,plain,(
% 2.10/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 2.10/0.65    inference(superposition,[],[f156,f109])).
% 2.10/0.65  fof(f243,plain,(
% 2.10/0.65    spl4_18 | ~spl4_7),
% 2.10/0.65    inference(avatar_split_clause,[],[f236,f159,f240])).
% 2.10/0.65  fof(f240,plain,(
% 2.10/0.65    spl4_18 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.10/0.65  fof(f236,plain,(
% 2.10/0.65    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_7),
% 2.10/0.65    inference(resolution,[],[f127,f161])).
% 2.10/0.65  fof(f127,plain,(
% 2.10/0.65    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f124])).
% 2.10/0.65  fof(f124,plain,(
% 2.10/0.65    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.65    inference(equality_resolution,[],[f103])).
% 2.10/0.65  fof(f103,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f64])).
% 2.10/0.65  fof(f208,plain,(
% 2.10/0.65    spl4_15 | ~spl4_10),
% 2.10/0.65    inference(avatar_split_clause,[],[f203,f174,f205])).
% 2.10/0.65  fof(f203,plain,(
% 2.10/0.65    v1_relat_1(sK2) | ~spl4_10),
% 2.10/0.65    inference(subsumption_resolution,[],[f195,f117])).
% 2.10/0.65  fof(f195,plain,(
% 2.10/0.65    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.10/0.65    inference(resolution,[],[f115,f176])).
% 2.10/0.65  fof(f202,plain,(
% 2.10/0.65    spl4_14 | ~spl4_7),
% 2.10/0.65    inference(avatar_split_clause,[],[f197,f159,f199])).
% 2.10/0.65  fof(f197,plain,(
% 2.10/0.65    v1_relat_1(sK3) | ~spl4_7),
% 2.10/0.65    inference(subsumption_resolution,[],[f194,f117])).
% 2.10/0.65  fof(f194,plain,(
% 2.10/0.65    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.10/0.65    inference(resolution,[],[f115,f161])).
% 2.10/0.65  fof(f193,plain,(
% 2.10/0.65    spl4_13 | ~spl4_5),
% 2.10/0.65    inference(avatar_split_clause,[],[f188,f149,f190])).
% 2.10/0.65  fof(f149,plain,(
% 2.10/0.65    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.10/0.65  fof(f188,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.10/0.65    inference(backward_demodulation,[],[f151,f105])).
% 2.10/0.65  fof(f151,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.10/0.65    inference(avatar_component_clause,[],[f149])).
% 2.10/0.65  fof(f187,plain,(
% 2.10/0.65    spl4_12),
% 2.10/0.65    inference(avatar_split_clause,[],[f68,f184])).
% 2.10/0.65  fof(f68,plain,(
% 2.10/0.65    v1_funct_1(sK2)),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f63,plain,(
% 2.10/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f62,f61])).
% 2.10/0.65  fof(f61,plain,(
% 2.10/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f62,plain,(
% 2.10/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f29,plain,(
% 2.10/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.10/0.65    inference(flattening,[],[f28])).
% 2.10/0.65  fof(f28,plain,(
% 2.10/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.10/0.65    inference(ennf_transformation,[],[f26])).
% 2.10/0.65  fof(f26,negated_conjecture,(
% 2.10/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.10/0.65    inference(negated_conjecture,[],[f25])).
% 2.10/0.65  fof(f25,conjecture,(
% 2.10/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.10/0.65  fof(f182,plain,(
% 2.10/0.65    spl4_11),
% 2.10/0.65    inference(avatar_split_clause,[],[f69,f179])).
% 2.10/0.65  fof(f69,plain,(
% 2.10/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f177,plain,(
% 2.10/0.65    spl4_10),
% 2.10/0.65    inference(avatar_split_clause,[],[f70,f174])).
% 2.10/0.65  fof(f70,plain,(
% 2.10/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f172,plain,(
% 2.10/0.65    spl4_9),
% 2.10/0.65    inference(avatar_split_clause,[],[f71,f169])).
% 2.10/0.65  fof(f71,plain,(
% 2.10/0.65    v1_funct_1(sK3)),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f167,plain,(
% 2.10/0.65    spl4_8),
% 2.10/0.65    inference(avatar_split_clause,[],[f72,f164])).
% 2.10/0.65  fof(f72,plain,(
% 2.10/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f162,plain,(
% 2.10/0.65    spl4_7),
% 2.10/0.65    inference(avatar_split_clause,[],[f73,f159])).
% 2.10/0.65  fof(f73,plain,(
% 2.10/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f157,plain,(
% 2.10/0.65    spl4_6),
% 2.10/0.65    inference(avatar_split_clause,[],[f74,f154])).
% 2.10/0.65  fof(f74,plain,(
% 2.10/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f152,plain,(
% 2.10/0.65    spl4_5),
% 2.10/0.65    inference(avatar_split_clause,[],[f75,f149])).
% 2.10/0.65  fof(f75,plain,(
% 2.10/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f147,plain,(
% 2.10/0.65    spl4_4),
% 2.10/0.65    inference(avatar_split_clause,[],[f76,f144])).
% 2.10/0.65  fof(f76,plain,(
% 2.10/0.65    v2_funct_1(sK2)),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f142,plain,(
% 2.10/0.65    ~spl4_3),
% 2.10/0.65    inference(avatar_split_clause,[],[f77,f139])).
% 2.10/0.65  fof(f77,plain,(
% 2.10/0.65    k1_xboole_0 != sK0),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f137,plain,(
% 2.10/0.65    ~spl4_2),
% 2.10/0.65    inference(avatar_split_clause,[],[f78,f134])).
% 2.10/0.65  fof(f78,plain,(
% 2.10/0.65    k1_xboole_0 != sK1),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  fof(f132,plain,(
% 2.10/0.65    ~spl4_1),
% 2.10/0.65    inference(avatar_split_clause,[],[f79,f129])).
% 2.10/0.65  fof(f79,plain,(
% 2.10/0.65    k2_funct_1(sK2) != sK3),
% 2.10/0.65    inference(cnf_transformation,[],[f63])).
% 2.10/0.65  % SZS output end Proof for theBenchmark
% 2.10/0.65  % (11554)------------------------------
% 2.10/0.65  % (11554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.65  % (11554)Termination reason: Refutation
% 2.10/0.65  
% 2.10/0.65  % (11554)Memory used [KB]: 7419
% 2.10/0.65  % (11554)Time elapsed: 0.201 s
% 2.10/0.65  % (11554)------------------------------
% 2.10/0.65  % (11554)------------------------------
% 2.10/0.66  % (11532)Success in time 0.283 s
%------------------------------------------------------------------------------
