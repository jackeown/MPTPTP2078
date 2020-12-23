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
% DateTime   : Thu Dec  3 13:14:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  339 ( 717 expanded)
%              Number of leaves         :   82 ( 337 expanded)
%              Depth                    :   12
%              Number of atoms          : 1107 (2640 expanded)
%              Number of equality atoms :  184 ( 591 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f178,f219,f225,f231,f237,f243,f284,f285,f286,f287,f288,f294,f303,f311,f348,f362,f376,f399,f407,f416,f443,f453,f458,f463,f483,f488,f490,f520,f554,f621,f627,f668,f673,f678,f683,f703,f871,f879,f886,f899,f924,f939,f968,f983,f1000,f1110,f1119,f1122])).

fof(f1122,plain,
    ( k1_xboole_0 != k1_relat_1(sK7)
    | sP4(k1_xboole_0,k2_relat_1(sK7),sK7)
    | ~ sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

% (27016)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f1119,plain,
    ( spl8_110
    | ~ spl8_109 ),
    inference(avatar_split_clause,[],[f1112,f1103,f1115])).

fof(f1115,plain,
    ( spl8_110
  <=> k1_xboole_0 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f1103,plain,
    ( spl8_109
  <=> sP0(k2_relat_1(sK7),k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f1112,plain,
    ( k1_xboole_0 = k1_relat_1(sK7)
    | ~ spl8_109 ),
    inference(resolution,[],[f1105,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1105,plain,
    ( sP0(k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ spl8_109 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f1110,plain,
    ( spl8_109
    | ~ spl8_97
    | ~ spl8_100
    | spl8_103 ),
    inference(avatar_split_clause,[],[f1109,f997,f936,f921,f1103])).

fof(f921,plain,
    ( spl8_97
  <=> sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f936,plain,
    ( spl8_100
  <=> v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f997,plain,
    ( spl8_103
  <=> k2_relat_1(sK7) = k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f1109,plain,
    ( sP0(k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ spl8_97
    | ~ spl8_100
    | spl8_103 ),
    inference(subsumption_resolution,[],[f1108,f923])).

fof(f923,plain,
    ( sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7))
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f921])).

fof(f1108,plain,
    ( sP0(k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7))
    | ~ spl8_100
    | spl8_103 ),
    inference(subsumption_resolution,[],[f1101,f938])).

fof(f938,plain,
    ( v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ spl8_100 ),
    inference(avatar_component_clause,[],[f936])).

fof(f1101,plain,
    ( ~ v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7))
    | sP0(k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7))
    | spl8_103 ),
    inference(trivial_inequality_removal,[],[f1100])).

fof(f1100,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | ~ v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7))
    | sP0(k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7))
    | spl8_103 ),
    inference(superposition,[],[f999,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f999,plain,
    ( k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))
    | spl8_103 ),
    inference(avatar_component_clause,[],[f997])).

fof(f1000,plain,
    ( ~ spl8_103
    | spl8_71
    | ~ spl8_102 ),
    inference(avatar_split_clause,[],[f986,f965,f665,f997])).

fof(f665,plain,
    ( spl8_71
  <=> k2_relat_1(sK7) = k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f965,plain,
    ( spl8_102
  <=> k2_funct_1(sK7) = k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f986,plain,
    ( k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))
    | spl8_71
    | ~ spl8_102 ),
    inference(backward_demodulation,[],[f667,f967])).

fof(f967,plain,
    ( k2_funct_1(sK7) = k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f965])).

fof(f667,plain,
    ( k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7))
    | spl8_71 ),
    inference(avatar_component_clause,[],[f665])).

fof(f983,plain,
    ( ~ spl8_3
    | ~ spl8_7
    | ~ spl8_40
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74
    | spl8_78 ),
    inference(avatar_contradiction_clause,[],[f982])).

fof(f982,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_40
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74
    | spl8_78 ),
    inference(subsumption_resolution,[],[f981,f140])).

fof(f140,plain,
    ( v1_funct_1(sK7)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_7
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f981,plain,
    ( ~ v1_funct_1(sK7)
    | ~ spl8_3
    | ~ spl8_40
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74
    | spl8_78 ),
    inference(subsumption_resolution,[],[f980,f682])).

fof(f682,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f680])).

fof(f680,plain,
    ( spl8_74
  <=> v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f980,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_3
    | ~ spl8_40
    | ~ spl8_72
    | ~ spl8_73
    | spl8_78 ),
    inference(subsumption_resolution,[],[f979,f677])).

fof(f677,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl8_73
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f979,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_3
    | ~ spl8_40
    | ~ spl8_72
    | spl8_78 ),
    inference(subsumption_resolution,[],[f978,f672])).

fof(f672,plain,
    ( k2_relat_1(sK7) = k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl8_72
  <=> k2_relat_1(sK7) = k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f978,plain,
    ( k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_3
    | ~ spl8_40
    | spl8_78 ),
    inference(subsumption_resolution,[],[f977,f120])).

fof(f120,plain,
    ( v2_funct_1(sK7)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f118])).

% (27020)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f118,plain,
    ( spl8_3
  <=> v2_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f977,plain,
    ( ~ v2_funct_1(sK7)
    | k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_40
    | spl8_78 ),
    inference(subsumption_resolution,[],[f959,f375])).

fof(f375,plain,
    ( k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl8_40
  <=> k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f959,plain,
    ( k1_relat_1(sK7) != k2_relat_1(k2_funct_1(sK7))
    | ~ v2_funct_1(sK7)
    | k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | spl8_78 ),
    inference(superposition,[],[f702,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f702,plain,
    ( k1_relat_1(sK7) != k2_relat_1(k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7))
    | spl8_78 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl8_78
  <=> k1_relat_1(sK7) = k2_relat_1(k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f968,plain,
    ( spl8_102
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f950,f680,f675,f670,f138,f118,f965])).

fof(f950,plain,
    ( k2_funct_1(sK7) = k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f140,f120,f682,f677,f672,f102])).

fof(f939,plain,
    ( spl8_100
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f901,f875,f936])).

fof(f875,plain,
    ( spl8_92
  <=> sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f901,plain,
    ( v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7))
    | ~ spl8_92 ),
    inference(unit_resulting_resolution,[],[f877,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f877,plain,
    ( sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f875])).

fof(f924,plain,
    ( spl8_97
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f904,f875,f921])).

fof(f904,plain,
    ( sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7))
    | ~ spl8_92 ),
    inference(unit_resulting_resolution,[],[f877,f337])).

fof(f337,plain,(
    ! [X4,X5,X3] :
      ( sP1(X4,k2_funct_1(X5),X3)
      | ~ sP4(X3,X4,X5) ) ),
    inference(resolution,[],[f100,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f44,f43,f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f899,plain,
    ( ~ spl8_95
    | ~ spl8_11
    | ~ spl8_38
    | spl8_51 ),
    inference(avatar_split_clause,[],[f887,f460,f359,f158,f896])).

fof(f896,plain,
    ( spl8_95
  <=> sP4(k1_xboole_0,k2_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f158,plain,
    ( spl8_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f359,plain,
    ( spl8_38
  <=> v1_partfun1(k2_funct_1(sK7),k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f460,plain,
    ( spl8_51
  <=> v1_xboole_0(k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f887,plain,
    ( ~ sP4(k1_xboole_0,k2_relat_1(sK7),sK7)
    | ~ spl8_11
    | ~ spl8_38
    | spl8_51 ),
    inference(unit_resulting_resolution,[],[f160,f462,f361,f390])).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X1,X0)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | ~ v1_partfun1(k2_funct_1(X0),X1) ) ),
    inference(resolution,[],[f80,f100])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

% (27018)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f361,plain,
    ( v1_partfun1(k2_funct_1(sK7),k2_relat_1(sK7))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f359])).

fof(f462,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK7))
    | spl8_51 ),
    inference(avatar_component_clause,[],[f460])).

fof(f160,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f886,plain,
    ( spl8_37
    | ~ spl8_92 ),
    inference(avatar_contradiction_clause,[],[f885])).

fof(f885,plain,
    ( $false
    | spl8_37
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f877,f377])).

fof(f377,plain,
    ( ! [X0] : ~ sP4(X0,k2_relat_1(sK7),sK7)
    | spl8_37 ),
    inference(unit_resulting_resolution,[],[f357,f339])).

fof(f339,plain,(
    ! [X10,X11,X9] :
      ( ~ sP4(X9,X10,X11)
      | v4_relat_1(k2_funct_1(X11),X10) ) ),
    inference(resolution,[],[f100,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f357,plain,
    ( ~ v4_relat_1(k2_funct_1(sK7),k2_relat_1(sK7))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl8_37
  <=> v4_relat_1(k2_funct_1(sK7),k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f879,plain,
    ( spl8_92
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f841,f680,f675,f670,f138,f118,f875])).

fof(f841,plain,
    ( sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f140,f120,f682,f672,f677,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP4(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f39,f48])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f871,plain,
    ( ~ spl8_3
    | ~ spl8_7
    | spl8_36
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f870])).

fof(f870,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_7
    | spl8_36
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f869,f140])).

fof(f869,plain,
    ( ~ v1_funct_1(sK7)
    | ~ spl8_3
    | spl8_36
    | ~ spl8_72
    | ~ spl8_73
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f868,f682])).

fof(f868,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_3
    | spl8_36
    | ~ spl8_72
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f867,f363])).

fof(f363,plain,
    ( ! [X0,X1] : ~ sP4(X0,X1,sK7)
    | spl8_36 ),
    inference(unit_resulting_resolution,[],[f353,f341])).

fof(f341,plain,(
    ! [X14,X12,X13] :
      ( ~ sP4(X12,X13,X14)
      | v1_relat_1(k2_funct_1(X14)) ) ),
    inference(subsumption_resolution,[],[f340,f77])).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f340,plain,(
    ! [X14,X12,X13] :
      ( ~ sP4(X12,X13,X14)
      | v1_relat_1(k2_funct_1(X14))
      | ~ v1_relat_1(k2_zfmisc_1(X13,X12)) ) ),
    inference(resolution,[],[f100,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f353,plain,
    ( ~ v1_relat_1(k2_funct_1(sK7))
    | spl8_36 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl8_36
  <=> v1_relat_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f867,plain,
    ( sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_3
    | ~ spl8_72
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f866,f120])).

fof(f866,plain,
    ( ~ v2_funct_1(sK7)
    | sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_72
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f848,f672])).

fof(f848,plain,
    ( k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ v2_funct_1(sK7)
    | sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ spl8_73 ),
    inference(resolution,[],[f101,f677])).

fof(f703,plain,
    ( ~ spl8_78
    | spl8_56
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f638,f624,f485,f700])).

fof(f485,plain,
    ( spl8_56
  <=> k2_struct_0(sK5) = k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f624,plain,
    ( spl8_67
  <=> k2_struct_0(sK5) = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f638,plain,
    ( k1_relat_1(sK7) != k2_relat_1(k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7))
    | spl8_56
    | ~ spl8_67 ),
    inference(backward_demodulation,[],[f487,f626])).

fof(f626,plain,
    ( k2_struct_0(sK5) = k1_relat_1(sK7)
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f624])).

fof(f487,plain,
    ( k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7))
    | spl8_56 ),
    inference(avatar_component_clause,[],[f485])).

fof(f683,plain,
    ( spl8_74
    | ~ spl8_50
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f634,f624,f455,f680])).

fof(f455,plain,
    ( spl8_50
  <=> v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f634,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))
    | ~ spl8_50
    | ~ spl8_67 ),
    inference(backward_demodulation,[],[f457,f626])).

fof(f457,plain,
    ( v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f455])).

fof(f678,plain,
    ( spl8_73
    | ~ spl8_49
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f633,f624,f450,f675])).

fof(f450,plain,
    ( spl8_49
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f633,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))
    | ~ spl8_49
    | ~ spl8_67 ),
    inference(backward_demodulation,[],[f452,f626])).

fof(f452,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f450])).

fof(f673,plain,
    ( spl8_72
    | ~ spl8_48
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f632,f624,f445,f670])).

fof(f445,plain,
    ( spl8_48
  <=> k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f632,plain,
    ( k2_relat_1(sK7) = k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)
    | ~ spl8_48
    | ~ spl8_67 ),
    inference(backward_demodulation,[],[f447,f626])).

fof(f447,plain,
    ( k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f445])).

fof(f668,plain,
    ( ~ spl8_71
    | spl8_47
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f631,f624,f440,f665])).

fof(f440,plain,
    ( spl8_47
  <=> k2_relat_1(sK7) = k1_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f631,plain,
    ( k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7))
    | spl8_47
    | ~ spl8_67 ),
    inference(backward_demodulation,[],[f442,f626])).

fof(f442,plain,
    ( k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7))
    | spl8_47 ),
    inference(avatar_component_clause,[],[f440])).

fof(f627,plain,
    ( spl8_67
    | ~ spl8_30
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f622,f610,f307,f298,f624])).

fof(f298,plain,
    ( spl8_30
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f307,plain,
    ( spl8_31
  <=> v4_relat_1(sK7,k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f610,plain,
    ( spl8_66
  <=> v1_partfun1(sK7,k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f622,plain,
    ( k2_struct_0(sK5) = k1_relat_1(sK7)
    | ~ spl8_30
    | ~ spl8_31
    | ~ spl8_66 ),
    inference(unit_resulting_resolution,[],[f300,f309,f612,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f612,plain,
    ( v1_partfun1(sK7,k2_struct_0(sK5))
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f610])).

fof(f309,plain,
    ( v4_relat_1(sK7,k2_struct_0(sK5))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f307])).

fof(f300,plain,
    ( v1_relat_1(sK7)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f298])).

fof(f621,plain,
    ( spl8_66
    | ~ spl8_7
    | ~ spl8_49
    | ~ spl8_50
    | spl8_51 ),
    inference(avatar_split_clause,[],[f620,f460,f455,f450,f138,f610])).

fof(f620,plain,
    ( v1_partfun1(sK7,k2_struct_0(sK5))
    | ~ spl8_7
    | ~ spl8_49
    | ~ spl8_50
    | spl8_51 ),
    inference(subsumption_resolution,[],[f619,f462])).

fof(f619,plain,
    ( v1_partfun1(sK7,k2_struct_0(sK5))
    | v1_xboole_0(k2_relat_1(sK7))
    | ~ spl8_7
    | ~ spl8_49
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f618,f140])).

fof(f618,plain,
    ( ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,k2_struct_0(sK5))
    | v1_xboole_0(k2_relat_1(sK7))
    | ~ spl8_49
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f608,f457])).

fof(f608,plain,
    ( ~ v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | v1_partfun1(sK7,k2_struct_0(sK5))
    | v1_xboole_0(k2_relat_1(sK7))
    | ~ spl8_49 ),
    inference(resolution,[],[f79,f452])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f554,plain,
    ( spl8_57
    | ~ spl8_7
    | ~ spl8_49
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f527,f455,f450,f138,f516])).

fof(f516,plain,
    ( spl8_57
  <=> sP3(k2_struct_0(sK5),k2_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f527,plain,
    ( sP3(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ spl8_7
    | ~ spl8_49
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f140,f457,f452,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f37,f46])).

% (27019)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f520,plain,
    ( ~ spl8_57
    | spl8_55 ),
    inference(avatar_split_clause,[],[f514,f480,f516])).

fof(f480,plain,
    ( spl8_55
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f514,plain,
    ( ~ sP3(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | spl8_55 ),
    inference(resolution,[],[f482,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f482,plain,
    ( ~ m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))
    | spl8_55 ),
    inference(avatar_component_clause,[],[f480])).

fof(f490,plain,
    ( spl8_48
    | ~ spl8_41
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f489,f402,f396,f445])).

fof(f396,plain,
    ( spl8_41
  <=> k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f402,plain,
    ( spl8_42
  <=> k2_struct_0(sK6) = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f489,plain,
    ( k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7)
    | ~ spl8_41
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f398,f404])).

fof(f404,plain,
    ( k2_struct_0(sK6) = k2_relat_1(sK7)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f402])).

fof(f398,plain,
    ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) = k2_relat_1(sK7)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f396])).

fof(f488,plain,
    ( ~ spl8_56
    | ~ spl8_42
    | spl8_44 ),
    inference(avatar_split_clause,[],[f428,f413,f402,f485])).

fof(f413,plain,
    ( spl8_44
  <=> k2_struct_0(sK5) = k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f428,plain,
    ( k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7))
    | ~ spl8_42
    | spl8_44 ),
    inference(backward_demodulation,[],[f415,f404])).

fof(f415,plain,
    ( k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_44 ),
    inference(avatar_component_clause,[],[f413])).

fof(f483,plain,
    ( ~ spl8_55
    | ~ spl8_42
    | spl8_43 ),
    inference(avatar_split_clause,[],[f427,f409,f402,f480])).

fof(f409,plain,
    ( spl8_43
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f427,plain,
    ( ~ m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))
    | ~ spl8_42
    | spl8_43 ),
    inference(backward_demodulation,[],[f411,f404])).

fof(f411,plain,
    ( ~ m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK5))))
    | spl8_43 ),
    inference(avatar_component_clause,[],[f409])).

fof(f463,plain,
    ( ~ spl8_51
    | spl8_29
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f423,f402,f291,f460])).

fof(f291,plain,
    ( spl8_29
  <=> v1_xboole_0(k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f423,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK7))
    | spl8_29
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f293,f404])).

fof(f293,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK6))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f291])).

fof(f458,plain,
    ( spl8_50
    | ~ spl8_28
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f422,f402,f275,f455])).

fof(f275,plain,
    ( spl8_28
  <=> v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f422,plain,
    ( v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))
    | ~ spl8_28
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f277,f404])).

fof(f277,plain,
    ( v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f275])).

fof(f453,plain,
    ( spl8_49
    | ~ spl8_27
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f421,f402,f270,f450])).

fof(f270,plain,
    ( spl8_27
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f421,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))
    | ~ spl8_27
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f272,f404])).

fof(f272,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f270])).

fof(f443,plain,
    ( ~ spl8_47
    | spl8_25
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f419,f402,f260,f440])).

fof(f260,plain,
    ( spl8_25
  <=> k2_struct_0(sK6) = k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f419,plain,
    ( k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7))
    | spl8_25
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f262,f404])).

fof(f262,plain,
    ( k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_25 ),
    inference(avatar_component_clause,[],[f260])).

fof(f416,plain,
    ( ~ spl8_43
    | ~ spl8_44
    | spl8_24 ),
    inference(avatar_split_clause,[],[f394,f255,f413,f409])).

fof(f255,plain,
    ( spl8_24
  <=> k2_struct_0(sK5) = k2_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f394,plain,
    ( k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK5))))
    | spl8_24 ),
    inference(superposition,[],[f257,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f257,plain,
    ( k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_24 ),
    inference(avatar_component_clause,[],[f255])).

fof(f407,plain,
    ( spl8_42
    | ~ spl8_26
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f406,f270,f265,f402])).

fof(f265,plain,
    ( spl8_26
  <=> k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f406,plain,
    ( k2_struct_0(sK6) = k2_relat_1(sK7)
    | ~ spl8_26
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f393,f272])).

fof(f393,plain,
    ( k2_struct_0(sK6) = k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))
    | ~ spl8_26 ),
    inference(superposition,[],[f267,f83])).

fof(f267,plain,
    ( k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f265])).

fof(f399,plain,
    ( spl8_41
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f391,f270,f396])).

fof(f391,plain,
    ( k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) = k2_relat_1(sK7)
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f272,f83])).

fof(f376,plain,
    ( spl8_40
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f371,f298,f138,f118,f373])).

fof(f371,plain,
    ( k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f300,f140,f120,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f362,plain,
    ( ~ spl8_36
    | ~ spl8_37
    | spl8_38
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f349,f345,f359,f355,f351])).

fof(f345,plain,
    ( spl8_35
  <=> k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f349,plain,
    ( v1_partfun1(k2_funct_1(sK7),k2_relat_1(sK7))
    | ~ v4_relat_1(k2_funct_1(sK7),k2_relat_1(sK7))
    | ~ v1_relat_1(k2_funct_1(sK7))
    | ~ spl8_35 ),
    inference(superposition,[],[f103,f347])).

fof(f347,plain,
    ( k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f345])).

fof(f103,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f348,plain,
    ( spl8_35
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f342,f298,f138,f118,f345])).

fof(f342,plain,
    ( k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7))
    | ~ spl8_3
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f300,f140,f120,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f311,plain,
    ( spl8_31
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f305,f270,f307])).

fof(f305,plain,
    ( v4_relat_1(sK7,k2_struct_0(sK5))
    | ~ spl8_27 ),
    inference(resolution,[],[f84,f272])).

fof(f303,plain,
    ( spl8_30
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f302,f270,f298])).

fof(f302,plain,
    ( v1_relat_1(sK7)
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f296,f77])).

fof(f296,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))
    | ~ spl8_27 ),
    inference(resolution,[],[f73,f272])).

fof(f294,plain,
    ( ~ spl8_29
    | ~ spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f289,f148,f143,f291])).

fof(f143,plain,
    ( spl8_8
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f148,plain,
    ( spl8_9
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f289,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK6))
    | ~ spl8_8
    | spl8_9 ),
    inference(unit_resulting_resolution,[],[f150,f145,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f145,plain,
    ( l1_struct_0(sK6)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f150,plain,
    ( ~ v2_struct_0(sK6)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f288,plain,
    ( spl8_28
    | ~ spl8_12
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f283,f240,f175,f275])).

fof(f175,plain,
    ( spl8_12
  <=> k2_struct_0(sK5) = u1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f240,plain,
    ( spl8_23
  <=> v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f283,plain,
    ( v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6))
    | ~ spl8_12
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f242,f177])).

% (27032)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f177,plain,
    ( k2_struct_0(sK5) = u1_struct_0(sK5)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f242,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f287,plain,
    ( spl8_27
    | ~ spl8_12
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f282,f234,f175,f270])).

fof(f234,plain,
    ( spl8_22
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f282,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))
    | ~ spl8_12
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f236,f177])).

fof(f236,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f234])).

fof(f286,plain,
    ( spl8_26
    | ~ spl8_12
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f281,f228,f175,f265])).

fof(f228,plain,
    ( spl8_21
  <=> k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f281,plain,
    ( k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7)
    | ~ spl8_12
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f230,f177])).

fof(f230,plain,
    ( k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f228])).

fof(f285,plain,
    ( ~ spl8_25
    | ~ spl8_12
    | spl8_20 ),
    inference(avatar_split_clause,[],[f280,f222,f175,f260])).

fof(f222,plain,
    ( spl8_20
  <=> k2_struct_0(sK6) = k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f280,plain,
    ( k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))
    | ~ spl8_12
    | spl8_20 ),
    inference(backward_demodulation,[],[f224,f177])).

fof(f224,plain,
    ( k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f222])).

fof(f284,plain,
    ( ~ spl8_24
    | ~ spl8_12
    | spl8_19 ),
    inference(avatar_split_clause,[],[f279,f216,f175,f255])).

fof(f216,plain,
    ( spl8_19
  <=> k2_struct_0(sK5) = k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f279,plain,
    ( k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))
    | ~ spl8_12
    | spl8_19 ),
    inference(backward_demodulation,[],[f218,f177])).

fof(f218,plain,
    ( k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_19 ),
    inference(avatar_component_clause,[],[f216])).

fof(f243,plain,
    ( spl8_23
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f238,f143,f133,f240])).

fof(f133,plain,
    ( spl8_6
  <=> v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f238,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6))
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f173,f145])).

fof(f173,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | ~ spl8_6 ),
    inference(superposition,[],[f135,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f135,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f237,plain,
    ( spl8_22
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f232,f143,f128,f234])).

fof(f128,plain,
    ( spl8_5
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f232,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f172,f145])).

fof(f172,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))
    | ~ l1_struct_0(sK6)
    | ~ spl8_5 ),
    inference(superposition,[],[f130,f72])).

fof(f130,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f231,plain,
    ( spl8_21
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f226,f143,f123,f228])).

fof(f123,plain,
    ( spl8_4
  <=> k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f226,plain,
    ( k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f171,f145])).

fof(f171,plain,
    ( k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7)
    | ~ l1_struct_0(sK6)
    | ~ spl8_4 ),
    inference(superposition,[],[f125,f72])).

fof(f125,plain,
    ( k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f225,plain,
    ( ~ spl8_20
    | spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f220,f143,f109,f222])).

fof(f109,plain,
    ( spl8_1
  <=> k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f220,plain,
    ( k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f170,f145])).

fof(f170,plain,
    ( k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))
    | ~ l1_struct_0(sK6)
    | spl8_1 ),
    inference(superposition,[],[f111,f72])).

fof(f111,plain,
    ( k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f219,plain,
    ( ~ spl8_19
    | spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f214,f143,f113,f216])).

fof(f113,plain,
    ( spl8_2
  <=> k2_struct_0(sK5) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f214,plain,
    ( k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))
    | spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f169,f145])).

% (27025)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f169,plain,
    ( k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))
    | ~ l1_struct_0(sK6)
    | spl8_2 ),
    inference(superposition,[],[f115,f72])).

fof(f115,plain,
    ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f178,plain,
    ( spl8_12
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f163,f153,f175])).

fof(f153,plain,
    ( spl8_10
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f163,plain,
    ( k2_struct_0(sK5) = u1_struct_0(sK5)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f155,f72])).

fof(f155,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f153])).

% (27015)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f161,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f71,f158])).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f156,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f62,f153])).

fof(f62,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))
      | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) )
    & v2_funct_1(sK7)
    & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
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
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

% (27032)Refutation not found, incomplete strategy% (27032)------------------------------
% (27032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27032)Termination reason: Refutation not found, incomplete strategy

% (27032)Memory used [KB]: 10618
% (27032)Time elapsed: 0.095 s
% (27032)------------------------------
% (27032)------------------------------
fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2))
            | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
          & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6))
          & v1_funct_1(X2) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2))
          | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
        & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))
        | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) )
      & v2_funct_1(sK7)
      & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
      & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

% (27029)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f151,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f63,f148])).

fof(f63,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f146,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f64,f143])).

fof(f64,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f141,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f65,f138])).

fof(f65,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f136,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f66,f133])).

fof(f66,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f131,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f67,f128])).

fof(f67,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f126,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f68,f123])).

fof(f68,plain,(
    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f69,f118])).

fof(f69,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f70,f113,f109])).

fof(f70,plain,
    ( k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))
    | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) ),
    inference(cnf_transformation,[],[f53])).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (27022)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (27014)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (27028)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (27017)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (27026)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (27013)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (27023)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (27012)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (27027)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (27028)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1123,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f178,f219,f225,f231,f237,f243,f284,f285,f286,f287,f288,f294,f303,f311,f348,f362,f376,f399,f407,f416,f443,f453,f458,f463,f483,f488,f490,f520,f554,f621,f627,f668,f673,f678,f683,f703,f871,f879,f886,f899,f924,f939,f968,f983,f1000,f1110,f1119,f1122])).
% 0.22/0.50  fof(f1122,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relat_1(sK7) | sP4(k1_xboole_0,k2_relat_1(sK7),sK7) | ~sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  % (27016)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  fof(f1119,plain,(
% 0.22/0.50    spl8_110 | ~spl8_109),
% 0.22/0.50    inference(avatar_split_clause,[],[f1112,f1103,f1115])).
% 0.22/0.50  fof(f1115,plain,(
% 0.22/0.50    spl8_110 <=> k1_xboole_0 = k1_relat_1(sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).
% 0.22/0.50  fof(f1103,plain,(
% 0.22/0.50    spl8_109 <=> sP0(k2_relat_1(sK7),k1_relat_1(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).
% 0.22/0.50  fof(f1112,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(sK7) | ~spl8_109),
% 0.22/0.50    inference(resolution,[],[f1105,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f1105,plain,(
% 0.22/0.50    sP0(k2_relat_1(sK7),k1_relat_1(sK7)) | ~spl8_109),
% 0.22/0.50    inference(avatar_component_clause,[],[f1103])).
% 0.22/0.50  fof(f1110,plain,(
% 0.22/0.50    spl8_109 | ~spl8_97 | ~spl8_100 | spl8_103),
% 0.22/0.50    inference(avatar_split_clause,[],[f1109,f997,f936,f921,f1103])).
% 0.22/0.50  fof(f921,plain,(
% 0.22/0.50    spl8_97 <=> sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).
% 0.22/0.50  fof(f936,plain,(
% 0.22/0.50    spl8_100 <=> v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).
% 0.22/0.50  fof(f997,plain,(
% 0.22/0.50    spl8_103 <=> k2_relat_1(sK7) = k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 0.22/0.50  fof(f1109,plain,(
% 0.22/0.50    sP0(k2_relat_1(sK7),k1_relat_1(sK7)) | (~spl8_97 | ~spl8_100 | spl8_103)),
% 0.22/0.50    inference(subsumption_resolution,[],[f1108,f923])).
% 0.22/0.50  fof(f923,plain,(
% 0.22/0.50    sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7)) | ~spl8_97),
% 0.22/0.50    inference(avatar_component_clause,[],[f921])).
% 0.22/0.50  fof(f1108,plain,(
% 0.22/0.50    sP0(k2_relat_1(sK7),k1_relat_1(sK7)) | ~sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7)) | (~spl8_100 | spl8_103)),
% 0.22/0.50    inference(subsumption_resolution,[],[f1101,f938])).
% 0.22/0.50  fof(f938,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7)) | ~spl8_100),
% 0.22/0.50    inference(avatar_component_clause,[],[f936])).
% 0.22/0.50  fof(f1101,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7)) | sP0(k2_relat_1(sK7),k1_relat_1(sK7)) | ~sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7)) | spl8_103),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f1100])).
% 0.22/0.50  fof(f1100,plain,(
% 0.22/0.50    k2_relat_1(sK7) != k2_relat_1(sK7) | ~v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7)) | sP0(k2_relat_1(sK7),k1_relat_1(sK7)) | ~sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7)) | spl8_103),
% 0.22/0.50    inference(superposition,[],[f999,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.22/0.50    inference(rectify,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f999,plain,(
% 0.22/0.50    k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) | spl8_103),
% 0.22/0.50    inference(avatar_component_clause,[],[f997])).
% 0.22/0.50  fof(f1000,plain,(
% 0.22/0.50    ~spl8_103 | spl8_71 | ~spl8_102),
% 0.22/0.50    inference(avatar_split_clause,[],[f986,f965,f665,f997])).
% 0.22/0.50  fof(f665,plain,(
% 0.22/0.50    spl8_71 <=> k2_relat_1(sK7) = k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).
% 0.22/0.50  fof(f965,plain,(
% 0.22/0.50    spl8_102 <=> k2_funct_1(sK7) = k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 0.22/0.50  fof(f986,plain,(
% 0.22/0.50    k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) | (spl8_71 | ~spl8_102)),
% 0.22/0.50    inference(backward_demodulation,[],[f667,f967])).
% 0.22/0.50  fof(f967,plain,(
% 0.22/0.50    k2_funct_1(sK7) = k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~spl8_102),
% 0.22/0.50    inference(avatar_component_clause,[],[f965])).
% 0.22/0.50  fof(f667,plain,(
% 0.22/0.50    k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)) | spl8_71),
% 0.22/0.50    inference(avatar_component_clause,[],[f665])).
% 0.22/0.50  fof(f983,plain,(
% 0.22/0.50    ~spl8_3 | ~spl8_7 | ~spl8_40 | ~spl8_72 | ~spl8_73 | ~spl8_74 | spl8_78),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f982])).
% 0.22/0.50  fof(f982,plain,(
% 0.22/0.50    $false | (~spl8_3 | ~spl8_7 | ~spl8_40 | ~spl8_72 | ~spl8_73 | ~spl8_74 | spl8_78)),
% 0.22/0.50    inference(subsumption_resolution,[],[f981,f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    v1_funct_1(sK7) | ~spl8_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl8_7 <=> v1_funct_1(sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.50  fof(f981,plain,(
% 0.22/0.50    ~v1_funct_1(sK7) | (~spl8_3 | ~spl8_40 | ~spl8_72 | ~spl8_73 | ~spl8_74 | spl8_78)),
% 0.22/0.50    inference(subsumption_resolution,[],[f980,f682])).
% 0.22/0.50  fof(f682,plain,(
% 0.22/0.50    v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~spl8_74),
% 0.22/0.50    inference(avatar_component_clause,[],[f680])).
% 0.22/0.50  fof(f680,plain,(
% 0.22/0.50    spl8_74 <=> v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).
% 0.22/0.50  fof(f980,plain,(
% 0.22/0.50    ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_3 | ~spl8_40 | ~spl8_72 | ~spl8_73 | spl8_78)),
% 0.22/0.50    inference(subsumption_resolution,[],[f979,f677])).
% 0.22/0.50  fof(f677,plain,(
% 0.22/0.50    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) | ~spl8_73),
% 0.22/0.50    inference(avatar_component_clause,[],[f675])).
% 0.22/0.50  fof(f675,plain,(
% 0.22/0.50    spl8_73 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).
% 0.22/0.50  fof(f979,plain,(
% 0.22/0.50    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_3 | ~spl8_40 | ~spl8_72 | spl8_78)),
% 0.22/0.50    inference(subsumption_resolution,[],[f978,f672])).
% 0.22/0.50  fof(f672,plain,(
% 0.22/0.50    k2_relat_1(sK7) = k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~spl8_72),
% 0.22/0.50    inference(avatar_component_clause,[],[f670])).
% 0.22/0.50  fof(f670,plain,(
% 0.22/0.50    spl8_72 <=> k2_relat_1(sK7) = k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).
% 0.22/0.50  fof(f978,plain,(
% 0.22/0.50    k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_3 | ~spl8_40 | spl8_78)),
% 0.22/0.50    inference(subsumption_resolution,[],[f977,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    v2_funct_1(sK7) | ~spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  % (27020)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl8_3 <=> v2_funct_1(sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.50  fof(f977,plain,(
% 0.22/0.50    ~v2_funct_1(sK7) | k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_40 | spl8_78)),
% 0.22/0.50    inference(subsumption_resolution,[],[f959,f375])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) | ~spl8_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f373])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    spl8_40 <=> k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.22/0.50  fof(f959,plain,(
% 0.22/0.50    k1_relat_1(sK7) != k2_relat_1(k2_funct_1(sK7)) | ~v2_funct_1(sK7) | k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | spl8_78),
% 0.22/0.50    inference(superposition,[],[f702,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f702,plain,(
% 0.22/0.50    k1_relat_1(sK7) != k2_relat_1(k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)) | spl8_78),
% 0.22/0.50    inference(avatar_component_clause,[],[f700])).
% 0.22/0.50  fof(f700,plain,(
% 0.22/0.50    spl8_78 <=> k1_relat_1(sK7) = k2_relat_1(k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 0.22/0.50  fof(f968,plain,(
% 0.22/0.50    spl8_102 | ~spl8_3 | ~spl8_7 | ~spl8_72 | ~spl8_73 | ~spl8_74),
% 0.22/0.50    inference(avatar_split_clause,[],[f950,f680,f675,f670,f138,f118,f965])).
% 0.22/0.50  fof(f950,plain,(
% 0.22/0.50    k2_funct_1(sK7) = k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | (~spl8_3 | ~spl8_7 | ~spl8_72 | ~spl8_73 | ~spl8_74)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f140,f120,f682,f677,f672,f102])).
% 0.22/0.50  fof(f939,plain,(
% 0.22/0.50    spl8_100 | ~spl8_92),
% 0.22/0.50    inference(avatar_split_clause,[],[f901,f875,f936])).
% 0.22/0.50  fof(f875,plain,(
% 0.22/0.50    spl8_92 <=> sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 0.22/0.50  fof(f901,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),k1_relat_1(sK7)) | ~spl8_92),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f877,f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP4(X0,X1,X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP4(X0,X1,X2))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.50  fof(f877,plain,(
% 0.22/0.50    sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~spl8_92),
% 0.22/0.50    inference(avatar_component_clause,[],[f875])).
% 0.22/0.50  fof(f924,plain,(
% 0.22/0.50    spl8_97 | ~spl8_92),
% 0.22/0.50    inference(avatar_split_clause,[],[f904,f875,f921])).
% 0.22/0.50  fof(f904,plain,(
% 0.22/0.50    sP1(k2_relat_1(sK7),k2_funct_1(sK7),k1_relat_1(sK7)) | ~spl8_92),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f877,f337])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (sP1(X4,k2_funct_1(X5),X3) | ~sP4(X3,X4,X5)) )),
% 0.22/0.51    inference(resolution,[],[f100,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(definition_folding,[],[f35,f44,f43,f42])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f61])).
% 0.22/0.51  fof(f899,plain,(
% 0.22/0.51    ~spl8_95 | ~spl8_11 | ~spl8_38 | spl8_51),
% 0.22/0.51    inference(avatar_split_clause,[],[f887,f460,f359,f158,f896])).
% 0.22/0.51  fof(f896,plain,(
% 0.22/0.51    spl8_95 <=> sP4(k1_xboole_0,k2_relat_1(sK7),sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    spl8_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    spl8_38 <=> v1_partfun1(k2_funct_1(sK7),k2_relat_1(sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.22/0.51  fof(f460,plain,(
% 0.22/0.51    spl8_51 <=> v1_xboole_0(k2_relat_1(sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.22/0.51  fof(f887,plain,(
% 0.22/0.51    ~sP4(k1_xboole_0,k2_relat_1(sK7),sK7) | (~spl8_11 | ~spl8_38 | spl8_51)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f160,f462,f361,f390])).
% 0.22/0.51  fof(f390,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP4(X2,X1,X0) | ~v1_xboole_0(X2) | v1_xboole_0(X1) | ~v1_partfun1(k2_funct_1(X0),X1)) )),
% 0.22/0.51    inference(resolution,[],[f80,f100])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  % (27018)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.22/0.51  fof(f361,plain,(
% 0.22/0.51    v1_partfun1(k2_funct_1(sK7),k2_relat_1(sK7)) | ~spl8_38),
% 0.22/0.51    inference(avatar_component_clause,[],[f359])).
% 0.22/0.51  fof(f462,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK7)) | spl8_51),
% 0.22/0.51    inference(avatar_component_clause,[],[f460])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0) | ~spl8_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f158])).
% 0.22/0.51  fof(f886,plain,(
% 0.22/0.51    spl8_37 | ~spl8_92),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f885])).
% 0.22/0.51  fof(f885,plain,(
% 0.22/0.51    $false | (spl8_37 | ~spl8_92)),
% 0.22/0.51    inference(subsumption_resolution,[],[f877,f377])).
% 0.22/0.51  fof(f377,plain,(
% 0.22/0.51    ( ! [X0] : (~sP4(X0,k2_relat_1(sK7),sK7)) ) | spl8_37),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f357,f339])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~sP4(X9,X10,X11) | v4_relat_1(k2_funct_1(X11),X10)) )),
% 0.22/0.51    inference(resolution,[],[f100,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    ~v4_relat_1(k2_funct_1(sK7),k2_relat_1(sK7)) | spl8_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f355])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    spl8_37 <=> v4_relat_1(k2_funct_1(sK7),k2_relat_1(sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.22/0.51  fof(f879,plain,(
% 0.22/0.51    spl8_92 | ~spl8_3 | ~spl8_7 | ~spl8_72 | ~spl8_73 | ~spl8_74),
% 0.22/0.51    inference(avatar_split_clause,[],[f841,f680,f675,f670,f138,f118,f875])).
% 0.22/0.51  fof(f841,plain,(
% 0.22/0.51    sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | (~spl8_3 | ~spl8_7 | ~spl8_72 | ~spl8_73 | ~spl8_74)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f140,f120,f682,f672,f677,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP4(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (sP4(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(definition_folding,[],[f39,f48])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.51  fof(f871,plain,(
% 0.22/0.51    ~spl8_3 | ~spl8_7 | spl8_36 | ~spl8_72 | ~spl8_73 | ~spl8_74),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f870])).
% 0.22/0.51  fof(f870,plain,(
% 0.22/0.51    $false | (~spl8_3 | ~spl8_7 | spl8_36 | ~spl8_72 | ~spl8_73 | ~spl8_74)),
% 0.22/0.51    inference(subsumption_resolution,[],[f869,f140])).
% 0.22/0.51  fof(f869,plain,(
% 0.22/0.51    ~v1_funct_1(sK7) | (~spl8_3 | spl8_36 | ~spl8_72 | ~spl8_73 | ~spl8_74)),
% 0.22/0.51    inference(subsumption_resolution,[],[f868,f682])).
% 0.22/0.51  fof(f868,plain,(
% 0.22/0.51    ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_3 | spl8_36 | ~spl8_72 | ~spl8_73)),
% 0.22/0.51    inference(subsumption_resolution,[],[f867,f363])).
% 0.22/0.51  fof(f363,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP4(X0,X1,sK7)) ) | spl8_36),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f353,f341])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ( ! [X14,X12,X13] : (~sP4(X12,X13,X14) | v1_relat_1(k2_funct_1(X14))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f340,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    ( ! [X14,X12,X13] : (~sP4(X12,X13,X14) | v1_relat_1(k2_funct_1(X14)) | ~v1_relat_1(k2_zfmisc_1(X13,X12))) )),
% 0.22/0.51    inference(resolution,[],[f100,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK7)) | spl8_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f351])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    spl8_36 <=> v1_relat_1(k2_funct_1(sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.22/0.51  fof(f867,plain,(
% 0.22/0.51    sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_3 | ~spl8_72 | ~spl8_73)),
% 0.22/0.51    inference(subsumption_resolution,[],[f866,f120])).
% 0.22/0.51  fof(f866,plain,(
% 0.22/0.51    ~v2_funct_1(sK7) | sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | (~spl8_72 | ~spl8_73)),
% 0.22/0.51    inference(subsumption_resolution,[],[f848,f672])).
% 0.22/0.51  fof(f848,plain,(
% 0.22/0.51    k2_relat_1(sK7) != k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~v2_funct_1(sK7) | sP4(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | ~v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | ~spl8_73),
% 0.22/0.51    inference(resolution,[],[f101,f677])).
% 0.22/0.51  fof(f703,plain,(
% 0.22/0.51    ~spl8_78 | spl8_56 | ~spl8_67),
% 0.22/0.51    inference(avatar_split_clause,[],[f638,f624,f485,f700])).
% 0.22/0.51  fof(f485,plain,(
% 0.22/0.51    spl8_56 <=> k2_struct_0(sK5) = k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 0.22/0.51  fof(f624,plain,(
% 0.22/0.51    spl8_67 <=> k2_struct_0(sK5) = k1_relat_1(sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 0.22/0.51  fof(f638,plain,(
% 0.22/0.51    k1_relat_1(sK7) != k2_relat_1(k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)) | (spl8_56 | ~spl8_67)),
% 0.22/0.51    inference(backward_demodulation,[],[f487,f626])).
% 0.22/0.51  fof(f626,plain,(
% 0.22/0.51    k2_struct_0(sK5) = k1_relat_1(sK7) | ~spl8_67),
% 0.22/0.51    inference(avatar_component_clause,[],[f624])).
% 0.22/0.51  fof(f487,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)) | spl8_56),
% 0.22/0.51    inference(avatar_component_clause,[],[f485])).
% 0.22/0.51  fof(f683,plain,(
% 0.22/0.51    spl8_74 | ~spl8_50 | ~spl8_67),
% 0.22/0.51    inference(avatar_split_clause,[],[f634,f624,f455,f680])).
% 0.22/0.51  fof(f455,plain,(
% 0.22/0.51    spl8_50 <=> v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.22/0.51  fof(f634,plain,(
% 0.22/0.51    v1_funct_2(sK7,k1_relat_1(sK7),k2_relat_1(sK7)) | (~spl8_50 | ~spl8_67)),
% 0.22/0.51    inference(backward_demodulation,[],[f457,f626])).
% 0.22/0.51  fof(f457,plain,(
% 0.22/0.51    v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~spl8_50),
% 0.22/0.51    inference(avatar_component_clause,[],[f455])).
% 0.22/0.51  fof(f678,plain,(
% 0.22/0.51    spl8_73 | ~spl8_49 | ~spl8_67),
% 0.22/0.51    inference(avatar_split_clause,[],[f633,f624,f450,f675])).
% 0.22/0.51  fof(f450,plain,(
% 0.22/0.51    spl8_49 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.22/0.51  fof(f633,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7)))) | (~spl8_49 | ~spl8_67)),
% 0.22/0.51    inference(backward_demodulation,[],[f452,f626])).
% 0.22/0.51  fof(f452,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | ~spl8_49),
% 0.22/0.51    inference(avatar_component_clause,[],[f450])).
% 0.22/0.51  fof(f673,plain,(
% 0.22/0.51    spl8_72 | ~spl8_48 | ~spl8_67),
% 0.22/0.51    inference(avatar_split_clause,[],[f632,f624,f445,f670])).
% 0.22/0.51  fof(f445,plain,(
% 0.22/0.51    spl8_48 <=> k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.22/0.51  fof(f632,plain,(
% 0.22/0.51    k2_relat_1(sK7) = k2_relset_1(k1_relat_1(sK7),k2_relat_1(sK7),sK7) | (~spl8_48 | ~spl8_67)),
% 0.22/0.51    inference(backward_demodulation,[],[f447,f626])).
% 0.22/0.51  fof(f447,plain,(
% 0.22/0.51    k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | ~spl8_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f445])).
% 0.22/0.51  fof(f668,plain,(
% 0.22/0.51    ~spl8_71 | spl8_47 | ~spl8_67),
% 0.22/0.51    inference(avatar_split_clause,[],[f631,f624,f440,f665])).
% 0.22/0.51  fof(f440,plain,(
% 0.22/0.51    spl8_47 <=> k2_relat_1(sK7) = k1_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.22/0.51  fof(f631,plain,(
% 0.22/0.51    k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_tops_2(k1_relat_1(sK7),k2_relat_1(sK7),sK7)) | (spl8_47 | ~spl8_67)),
% 0.22/0.51    inference(backward_demodulation,[],[f442,f626])).
% 0.22/0.51  fof(f442,plain,(
% 0.22/0.51    k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)) | spl8_47),
% 0.22/0.51    inference(avatar_component_clause,[],[f440])).
% 0.22/0.51  fof(f627,plain,(
% 0.22/0.51    spl8_67 | ~spl8_30 | ~spl8_31 | ~spl8_66),
% 0.22/0.51    inference(avatar_split_clause,[],[f622,f610,f307,f298,f624])).
% 0.22/0.51  fof(f298,plain,(
% 0.22/0.51    spl8_30 <=> v1_relat_1(sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    spl8_31 <=> v4_relat_1(sK7,k2_struct_0(sK5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.22/0.51  fof(f610,plain,(
% 0.22/0.51    spl8_66 <=> v1_partfun1(sK7,k2_struct_0(sK5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 0.22/0.51  fof(f622,plain,(
% 0.22/0.51    k2_struct_0(sK5) = k1_relat_1(sK7) | (~spl8_30 | ~spl8_31 | ~spl8_66)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f300,f309,f612,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.51  fof(f612,plain,(
% 0.22/0.51    v1_partfun1(sK7,k2_struct_0(sK5)) | ~spl8_66),
% 0.22/0.51    inference(avatar_component_clause,[],[f610])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    v4_relat_1(sK7,k2_struct_0(sK5)) | ~spl8_31),
% 0.22/0.51    inference(avatar_component_clause,[],[f307])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    v1_relat_1(sK7) | ~spl8_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f298])).
% 0.22/0.51  fof(f621,plain,(
% 0.22/0.51    spl8_66 | ~spl8_7 | ~spl8_49 | ~spl8_50 | spl8_51),
% 0.22/0.51    inference(avatar_split_clause,[],[f620,f460,f455,f450,f138,f610])).
% 0.22/0.51  fof(f620,plain,(
% 0.22/0.51    v1_partfun1(sK7,k2_struct_0(sK5)) | (~spl8_7 | ~spl8_49 | ~spl8_50 | spl8_51)),
% 0.22/0.51    inference(subsumption_resolution,[],[f619,f462])).
% 0.22/0.51  fof(f619,plain,(
% 0.22/0.51    v1_partfun1(sK7,k2_struct_0(sK5)) | v1_xboole_0(k2_relat_1(sK7)) | (~spl8_7 | ~spl8_49 | ~spl8_50)),
% 0.22/0.51    inference(subsumption_resolution,[],[f618,f140])).
% 0.22/0.51  fof(f618,plain,(
% 0.22/0.51    ~v1_funct_1(sK7) | v1_partfun1(sK7,k2_struct_0(sK5)) | v1_xboole_0(k2_relat_1(sK7)) | (~spl8_49 | ~spl8_50)),
% 0.22/0.51    inference(subsumption_resolution,[],[f608,f457])).
% 0.22/0.51  fof(f608,plain,(
% 0.22/0.51    ~v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | v1_partfun1(sK7,k2_struct_0(sK5)) | v1_xboole_0(k2_relat_1(sK7)) | ~spl8_49),
% 0.22/0.51    inference(resolution,[],[f79,f452])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.51  fof(f554,plain,(
% 0.22/0.51    spl8_57 | ~spl8_7 | ~spl8_49 | ~spl8_50),
% 0.22/0.51    inference(avatar_split_clause,[],[f527,f455,f450,f138,f516])).
% 0.22/0.51  fof(f516,plain,(
% 0.22/0.51    spl8_57 <=> sP3(k2_struct_0(sK5),k2_relat_1(sK7),sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 0.22/0.51  fof(f527,plain,(
% 0.22/0.51    sP3(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | (~spl8_7 | ~spl8_49 | ~spl8_50)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f140,f457,f452,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (sP3(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(definition_folding,[],[f37,f46])).
% 0.22/0.51  % (27019)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP3(X0,X1,X2))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.51  fof(f520,plain,(
% 0.22/0.51    ~spl8_57 | spl8_55),
% 0.22/0.51    inference(avatar_split_clause,[],[f514,f480,f516])).
% 0.22/0.51  fof(f480,plain,(
% 0.22/0.51    spl8_55 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 0.22/0.51  fof(f514,plain,(
% 0.22/0.51    ~sP3(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | spl8_55),
% 0.22/0.51    inference(resolution,[],[f482,f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP3(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP3(X0,X1,X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f46])).
% 0.22/0.51  fof(f482,plain,(
% 0.22/0.51    ~m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) | spl8_55),
% 0.22/0.51    inference(avatar_component_clause,[],[f480])).
% 0.22/0.51  fof(f490,plain,(
% 0.22/0.51    spl8_48 | ~spl8_41 | ~spl8_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f489,f402,f396,f445])).
% 0.22/0.51  fof(f396,plain,(
% 0.22/0.51    spl8_41 <=> k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) = k2_relat_1(sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    spl8_42 <=> k2_struct_0(sK6) = k2_relat_1(sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.22/0.51  fof(f489,plain,(
% 0.22/0.51    k2_relat_1(sK7) = k2_relset_1(k2_struct_0(sK5),k2_relat_1(sK7),sK7) | (~spl8_41 | ~spl8_42)),
% 0.22/0.51    inference(forward_demodulation,[],[f398,f404])).
% 0.22/0.51  fof(f404,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relat_1(sK7) | ~spl8_42),
% 0.22/0.51    inference(avatar_component_clause,[],[f402])).
% 0.22/0.51  fof(f398,plain,(
% 0.22/0.51    k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) = k2_relat_1(sK7) | ~spl8_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f396])).
% 0.22/0.51  fof(f488,plain,(
% 0.22/0.51    ~spl8_56 | ~spl8_42 | spl8_44),
% 0.22/0.51    inference(avatar_split_clause,[],[f428,f413,f402,f485])).
% 0.22/0.51  fof(f413,plain,(
% 0.22/0.51    spl8_44 <=> k2_struct_0(sK5) = k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 0.22/0.51  fof(f428,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)) | (~spl8_42 | spl8_44)),
% 0.22/0.51    inference(backward_demodulation,[],[f415,f404])).
% 0.22/0.51  fof(f415,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) | spl8_44),
% 0.22/0.51    inference(avatar_component_clause,[],[f413])).
% 0.22/0.51  fof(f483,plain,(
% 0.22/0.51    ~spl8_55 | ~spl8_42 | spl8_43),
% 0.22/0.51    inference(avatar_split_clause,[],[f427,f409,f402,f480])).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    spl8_43 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK5))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.22/0.51  fof(f427,plain,(
% 0.22/0.51    ~m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_struct_0(sK5)))) | (~spl8_42 | spl8_43)),
% 0.22/0.51    inference(backward_demodulation,[],[f411,f404])).
% 0.22/0.51  fof(f411,plain,(
% 0.22/0.51    ~m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK5)))) | spl8_43),
% 0.22/0.51    inference(avatar_component_clause,[],[f409])).
% 0.22/0.51  fof(f463,plain,(
% 0.22/0.51    ~spl8_51 | spl8_29 | ~spl8_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f423,f402,f291,f460])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    spl8_29 <=> v1_xboole_0(k2_struct_0(sK6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.22/0.51  fof(f423,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK7)) | (spl8_29 | ~spl8_42)),
% 0.22/0.51    inference(backward_demodulation,[],[f293,f404])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_struct_0(sK6)) | spl8_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f291])).
% 0.22/0.51  fof(f458,plain,(
% 0.22/0.51    spl8_50 | ~spl8_28 | ~spl8_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f422,f402,f275,f455])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    spl8_28 <=> v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.22/0.51  fof(f422,plain,(
% 0.22/0.51    v1_funct_2(sK7,k2_struct_0(sK5),k2_relat_1(sK7)) | (~spl8_28 | ~spl8_42)),
% 0.22/0.51    inference(backward_demodulation,[],[f277,f404])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6)) | ~spl8_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f275])).
% 0.22/0.51  fof(f453,plain,(
% 0.22/0.51    spl8_49 | ~spl8_27 | ~spl8_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f421,f402,f270,f450])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl8_27 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.22/0.51  fof(f421,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_relat_1(sK7)))) | (~spl8_27 | ~spl8_42)),
% 0.22/0.51    inference(backward_demodulation,[],[f272,f404])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) | ~spl8_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f270])).
% 0.22/0.51  fof(f443,plain,(
% 0.22/0.51    ~spl8_47 | spl8_25 | ~spl8_42),
% 0.22/0.51    inference(avatar_split_clause,[],[f419,f402,f260,f440])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    spl8_25 <=> k2_struct_0(sK6) = k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.51  fof(f419,plain,(
% 0.22/0.51    k2_relat_1(sK7) != k1_relset_1(k2_relat_1(sK7),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_relat_1(sK7),sK7)) | (spl8_25 | ~spl8_42)),
% 0.22/0.51    inference(backward_demodulation,[],[f262,f404])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) | spl8_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f260])).
% 0.22/0.51  fof(f416,plain,(
% 0.22/0.51    ~spl8_43 | ~spl8_44 | spl8_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f394,f255,f413,f409])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    spl8_24 <=> k2_struct_0(sK5) = k2_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.51  fof(f394,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relat_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK5)))) | spl8_24),
% 0.22/0.51    inference(superposition,[],[f257,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) | spl8_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f255])).
% 0.22/0.51  fof(f407,plain,(
% 0.22/0.51    spl8_42 | ~spl8_26 | ~spl8_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f406,f270,f265,f402])).
% 0.22/0.51  fof(f265,plain,(
% 0.22/0.51    spl8_26 <=> k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relat_1(sK7) | (~spl8_26 | ~spl8_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f393,f272])).
% 0.22/0.51  fof(f393,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) | ~spl8_26),
% 0.22/0.51    inference(superposition,[],[f267,f83])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) | ~spl8_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f265])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    spl8_41 | ~spl8_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f391,f270,f396])).
% 0.22/0.51  fof(f391,plain,(
% 0.22/0.51    k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) = k2_relat_1(sK7) | ~spl8_27),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f272,f83])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    spl8_40 | ~spl8_3 | ~spl8_7 | ~spl8_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f371,f298,f138,f118,f373])).
% 0.22/0.51  fof(f371,plain,(
% 0.22/0.51    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) | (~spl8_3 | ~spl8_7 | ~spl8_30)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f300,f140,f120,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    ~spl8_36 | ~spl8_37 | spl8_38 | ~spl8_35),
% 0.22/0.51    inference(avatar_split_clause,[],[f349,f345,f359,f355,f351])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    spl8_35 <=> k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    v1_partfun1(k2_funct_1(sK7),k2_relat_1(sK7)) | ~v4_relat_1(k2_funct_1(sK7),k2_relat_1(sK7)) | ~v1_relat_1(k2_funct_1(sK7)) | ~spl8_35),
% 0.22/0.51    inference(superposition,[],[f103,f347])).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7)) | ~spl8_35),
% 0.22/0.51    inference(avatar_component_clause,[],[f345])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f54])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    spl8_35 | ~spl8_3 | ~spl8_7 | ~spl8_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f342,f298,f138,f118,f345])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7)) | (~spl8_3 | ~spl8_7 | ~spl8_30)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f300,f140,f120,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    spl8_31 | ~spl8_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f305,f270,f307])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    v4_relat_1(sK7,k2_struct_0(sK5)) | ~spl8_27),
% 0.22/0.51    inference(resolution,[],[f84,f272])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    spl8_30 | ~spl8_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f302,f270,f298])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    v1_relat_1(sK7) | ~spl8_27),
% 0.22/0.51    inference(subsumption_resolution,[],[f296,f77])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6))) | ~spl8_27),
% 0.22/0.51    inference(resolution,[],[f73,f272])).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    ~spl8_29 | ~spl8_8 | spl8_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f289,f148,f143,f291])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl8_8 <=> l1_struct_0(sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    spl8_9 <=> v2_struct_0(sK6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_struct_0(sK6)) | (~spl8_8 | spl8_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f150,f145,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    l1_struct_0(sK6) | ~spl8_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f143])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~v2_struct_0(sK6) | spl8_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f148])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    spl8_28 | ~spl8_12 | ~spl8_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f283,f240,f175,f275])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    spl8_12 <=> k2_struct_0(sK5) = u1_struct_0(sK5)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    spl8_23 <=> v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    v1_funct_2(sK7,k2_struct_0(sK5),k2_struct_0(sK6)) | (~spl8_12 | ~spl8_23)),
% 0.22/0.51    inference(backward_demodulation,[],[f242,f177])).
% 0.22/0.51  % (27032)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    k2_struct_0(sK5) = u1_struct_0(sK5) | ~spl8_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f175])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6)) | ~spl8_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f240])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    spl8_27 | ~spl8_12 | ~spl8_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f282,f234,f175,f270])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    spl8_22 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK6)))) | (~spl8_12 | ~spl8_22)),
% 0.22/0.51    inference(backward_demodulation,[],[f236,f177])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) | ~spl8_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f234])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    spl8_26 | ~spl8_12 | ~spl8_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f281,f228,f175,f265])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    spl8_21 <=> k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(k2_struct_0(sK5),k2_struct_0(sK6),sK7) | (~spl8_12 | ~spl8_21)),
% 0.22/0.51    inference(backward_demodulation,[],[f230,f177])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7) | ~spl8_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f228])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    ~spl8_25 | ~spl8_12 | spl8_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f280,f222,f175,f260])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    spl8_20 <=> k2_struct_0(sK6) = k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) | (~spl8_12 | spl8_20)),
% 0.22/0.51    inference(backward_demodulation,[],[f224,f177])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) | spl8_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f222])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    ~spl8_24 | ~spl8_12 | spl8_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f279,f216,f175,f255])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    spl8_19 <=> k2_struct_0(sK5) = k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),k2_struct_0(sK5),k2_tops_2(k2_struct_0(sK5),k2_struct_0(sK6),sK7)) | (~spl8_12 | spl8_19)),
% 0.22/0.51    inference(backward_demodulation,[],[f218,f177])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) | spl8_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f216])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    spl8_23 | ~spl8_6 | ~spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f238,f143,f133,f240])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl8_6 <=> v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6)) | (~spl8_6 | ~spl8_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f145])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    v1_funct_2(sK7,u1_struct_0(sK5),k2_struct_0(sK6)) | ~l1_struct_0(sK6) | ~spl8_6),
% 0.22/0.51    inference(superposition,[],[f135,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) | ~spl8_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f133])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    spl8_22 | ~spl8_5 | ~spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f232,f143,f128,f234])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    spl8_5 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) | (~spl8_5 | ~spl8_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f145])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK6)))) | ~l1_struct_0(sK6) | ~spl8_5),
% 0.22/0.51    inference(superposition,[],[f130,f72])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) | ~spl8_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f128])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    spl8_21 | ~spl8_4 | ~spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f226,f143,f123,f228])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl8_4 <=> k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7) | (~spl8_4 | ~spl8_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f145])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),k2_struct_0(sK6),sK7) | ~l1_struct_0(sK6) | ~spl8_4),
% 0.22/0.51    inference(superposition,[],[f125,f72])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) | ~spl8_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    ~spl8_20 | spl8_1 | ~spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f220,f143,f109,f222])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl8_1 <=> k2_struct_0(sK6) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) | (spl8_1 | ~spl8_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f145])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    k2_struct_0(sK6) != k1_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) | ~l1_struct_0(sK6) | spl8_1),
% 0.22/0.51    inference(superposition,[],[f111,f72])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) | spl8_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ~spl8_19 | spl8_2 | ~spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f214,f143,f113,f216])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl8_2 <=> k2_struct_0(sK5) = k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) | (spl8_2 | ~spl8_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f145])).
% 0.22/0.51  % (27025)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(k2_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),k2_struct_0(sK6),sK7)) | ~l1_struct_0(sK6) | spl8_2),
% 0.22/0.51    inference(superposition,[],[f115,f72])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) | spl8_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f113])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    spl8_12 | ~spl8_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f163,f153,f175])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    spl8_10 <=> l1_struct_0(sK5)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    k2_struct_0(sK5) = u1_struct_0(sK5) | ~spl8_10),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f155,f72])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    l1_struct_0(sK5) | ~spl8_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f153])).
% 0.22/0.51  % (27015)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl8_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f71,f158])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    spl8_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f153])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    l1_struct_0(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    (((k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))) & v2_funct_1(sK7) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)) & l1_struct_0(sK5)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f52,f51,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK5) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK5))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (27032)Refutation not found, incomplete strategy% (27032)------------------------------
% 0.22/0.51  % (27032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27032)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27032)Memory used [KB]: 10618
% 0.22/0.51  % (27032)Time elapsed: 0.095 s
% 0.22/0.51  % (27032)------------------------------
% 0.22/0.51  % (27032)------------------------------
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : ((k2_struct_0(sK5) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)) | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2))) & v2_funct_1(X2) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ? [X2] : ((k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2)) | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),X2))) & v2_funct_1(X2) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(X2)) => ((k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))) & v2_funct_1(sK7) & k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (27029)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ~spl8_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f63,f148])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ~v2_struct_0(sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f143])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    l1_struct_0(sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl8_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f138])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    v1_funct_1(sK7)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    spl8_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f133])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl8_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f67,f128])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    spl8_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f68,f123])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    k2_struct_0(sK6) = k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK7)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl8_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f118])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    v2_funct_1(sK7)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ~spl8_1 | ~spl8_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f113,f109])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    k2_struct_0(sK5) != k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7)) | k2_struct_0(sK6) != k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),k2_tops_2(u1_struct_0(sK5),u1_struct_0(sK6),sK7))),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27028)------------------------------
% 0.22/0.51  % (27028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27028)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27028)Memory used [KB]: 11513
% 0.22/0.51  % (27028)Time elapsed: 0.060 s
% 0.22/0.51  % (27028)------------------------------
% 0.22/0.51  % (27028)------------------------------
% 0.22/0.52  % (27011)Success in time 0.154 s
%------------------------------------------------------------------------------
