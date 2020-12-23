%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 557 expanded)
%              Number of leaves         :   60 ( 230 expanded)
%              Depth                    :   15
%              Number of atoms          : 1169 (1988 expanded)
%              Number of equality atoms :  160 ( 298 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f615,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f117,f122,f127,f132,f137,f158,f164,f187,f199,f204,f219,f221,f222,f251,f263,f264,f277,f287,f300,f346,f363,f403,f423,f441,f446,f470,f482,f494,f542,f554,f607,f608,f614])).

fof(f614,plain,
    ( ~ spl3_1
    | ~ spl3_33
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_33
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f612,f402])).

fof(f402,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl3_40
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f612,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f611,f87])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f611,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_33
    | ~ spl3_41 ),
    inference(resolution,[],[f358,f422])).

fof(f422,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl3_41
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl3_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f608,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f607,plain,
    ( spl3_57
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_47
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f602,f484,f458,f431,f297,f284,f274,f151,f604])).

fof(f604,plain,
    ( spl3_57
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f151,plain,
    ( spl3_12
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f274,plain,
    ( spl3_26
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f284,plain,
    ( spl3_27
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f297,plain,
    ( spl3_30
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f431,plain,
    ( spl3_43
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f458,plain,
    ( spl3_47
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f484,plain,
    ( spl3_49
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f602,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_47
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f558,f459])).

fof(f459,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f458])).

fof(f558,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_43
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f557,f486])).

fof(f486,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f484])).

fof(f557,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f556,f286])).

fof(f286,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f284])).

fof(f556,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f555,f286])).

fof(f555,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_30
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f317,f432])).

fof(f432,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f431])).

fof(f317,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f316,f153])).

fof(f153,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f316,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f309,f276])).

fof(f276,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f274])).

fof(f309,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(resolution,[],[f299,f81])).

% (6118)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f299,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f297])).

fof(f554,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | spl3_54 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | spl3_54 ),
    inference(subsumption_resolution,[],[f552,f156])).

fof(f156,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f552,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_54 ),
    inference(subsumption_resolution,[],[f551,f92])).

fof(f92,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f551,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_54 ),
    inference(subsumption_resolution,[],[f550,f87])).

fof(f550,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_54 ),
    inference(trivial_inequality_removal,[],[f549])).

fof(f549,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_54 ),
    inference(superposition,[],[f541,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f541,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl3_54
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f542,plain,
    ( ~ spl3_54
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(avatar_split_clause,[],[f525,f458,f454,f431,f155,f90,f85,f539])).

fof(f454,plain,
    ( spl3_46
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f525,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(subsumption_resolution,[],[f524,f92])).

fof(f524,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(subsumption_resolution,[],[f523,f156])).

fof(f523,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(subsumption_resolution,[],[f522,f87])).

fof(f522,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(subsumption_resolution,[],[f521,f58])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f521,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(duplicate_literal_removal,[],[f520])).

fof(f520,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(superposition,[],[f476,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f476,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_43
    | ~ spl3_46
    | spl3_47 ),
    inference(subsumption_resolution,[],[f475,f455])).

fof(f455,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f454])).

fof(f475,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_43
    | spl3_47 ),
    inference(subsumption_resolution,[],[f472,f432])).

fof(f472,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | spl3_47 ),
    inference(resolution,[],[f460,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f460,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f458])).

fof(f494,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f482,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | spl3_48 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | spl3_48 ),
    inference(subsumption_resolution,[],[f480,f156])).

fof(f480,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_48 ),
    inference(subsumption_resolution,[],[f479,f92])).

fof(f479,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_48 ),
    inference(subsumption_resolution,[],[f478,f87])).

fof(f478,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_48 ),
    inference(trivial_inequality_removal,[],[f477])).

fof(f477,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_48 ),
    inference(superposition,[],[f463,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f463,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl3_48
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f470,plain,
    ( ~ spl3_1
    | ~ spl3_13
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_13
    | spl3_46 ),
    inference(subsumption_resolution,[],[f468,f156])).

fof(f468,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_46 ),
    inference(subsumption_resolution,[],[f466,f87])).

fof(f466,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_46 ),
    inference(resolution,[],[f456,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f456,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f454])).

fof(f446,plain,
    ( spl3_44
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f418,f297,f284,f443])).

fof(f443,plain,
    ( spl3_44
  <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f418,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f304,f286])).

fof(f304,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(resolution,[],[f299,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f441,plain,
    ( ~ spl3_1
    | ~ spl3_13
    | spl3_43 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_13
    | spl3_43 ),
    inference(subsumption_resolution,[],[f439,f156])).

fof(f439,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_43 ),
    inference(subsumption_resolution,[],[f436,f87])).

fof(f436,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_43 ),
    inference(resolution,[],[f433,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f433,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f431])).

fof(f423,plain,
    ( spl3_41
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f324,f284,f260,f420])).

fof(f260,plain,
    ( spl3_25
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f324,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(superposition,[],[f261,f286])).

fof(f261,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f260])).

fof(f403,plain,
    ( spl3_40
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f389,f284,f214,f161,f400])).

fof(f161,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f214,plain,
    ( spl3_21
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f389,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f236,f286])).

fof(f236,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(superposition,[],[f163,f216])).

fof(f216,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f163,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f363,plain,
    ( spl3_33
    | spl3_34
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f355,f284,f260,f214,f161,f85,f360,f357])).

fof(f360,plain,
    ( spl3_34
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f355,plain,
    ( ! [X0] :
        ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f354,f286])).

fof(f354,plain,
    ( ! [X0] :
        ( r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f353,f216])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f352,f286])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f351,f216])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f350,f286])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f349,f216])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f348,f261])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f181,f216])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f173,f87])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f346,plain,
    ( spl3_32
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f336,f284,f260,f214,f210,f161,f90,f85,f343])).

fof(f343,plain,
    ( spl3_32
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f210,plain,
    ( spl3_20
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f336,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f335,f286])).

fof(f335,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f334,f216])).

fof(f334,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f333,f212])).

fof(f212,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f333,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f332,f216])).

fof(f332,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f331,f261])).

fof(f331,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f180,f216])).

fof(f180,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f179,f92])).

fof(f179,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f172,f87])).

fof(f172,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f81])).

fof(f300,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f282,f260,f214,f210,f161,f90,f85,f297])).

fof(f282,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f281,f216])).

fof(f281,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f280,f212])).

fof(f280,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f279,f216])).

fof(f279,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f278,f261])).

fof(f278,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f178,f216])).

fof(f178,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f177,f92])).

fof(f177,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f171,f87])).

fof(f171,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    ( spl3_27
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f267,f256,f184,f155,f284])).

fof(f184,plain,
    ( spl3_15
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f256,plain,
    ( spl3_24
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f267,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f266,f156])).

fof(f266,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f265,f186])).

fof(f186,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f265,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f258,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f258,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f256])).

fof(f277,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f272,f260,f214,f210,f161,f90,f85,f274])).

fof(f272,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f271,f216])).

fof(f271,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f270,f212])).

fof(f270,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f269,f216])).

fof(f269,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f268,f261])).

fof(f268,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f176,f216])).

fof(f176,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f175,f92])).

fof(f175,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f170,f87])).

fof(f170,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f264,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f263,plain,
    ( spl3_24
    | ~ spl3_25
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | spl3_23 ),
    inference(avatar_split_clause,[],[f254,f248,f214,f161,f85,f260,f256])).

fof(f248,plain,
    ( spl3_23
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f254,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | spl3_23 ),
    inference(forward_demodulation,[],[f253,f216])).

fof(f253,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21
    | spl3_23 ),
    inference(subsumption_resolution,[],[f252,f250])).

fof(f250,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f252,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f174,f216])).

fof(f174,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f166,f87])).

fof(f166,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f251,plain,
    ( ~ spl3_23
    | spl3_3
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f239,f214,f100,f95,f248])).

fof(f95,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f239,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f238,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f238,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f237,f102])).

fof(f102,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f237,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_21 ),
    inference(superposition,[],[f61,f216])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f222,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f221,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f219,plain,
    ( spl3_13
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f217,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f217,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_13
    | ~ spl3_14 ),
    inference(resolution,[],[f165,f163])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_13 ),
    inference(resolution,[],[f157,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f157,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f204,plain,
    ( spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f167,f161,f201])).

fof(f201,plain,
    ( spl3_18
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f167,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f75])).

fof(f199,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f189,f129,f119,f196])).

fof(f196,plain,
    ( spl3_17
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f119,plain,
    ( spl3_7
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f189,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f188,f131])).

fof(f131,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f188,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f53,f121])).

fof(f121,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f53,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
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
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f187,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f168,f161,f184])).

fof(f168,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f163,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f164,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f147,f129,f124,f119,f161])).

fof(f124,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f143,f131])).

fof(f143,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f126,f121])).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f158,plain,
    ( spl3_12
    | ~ spl3_13
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f110,f90,f85,f155,f151])).

fof(f110,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f109,f87])).

fof(f109,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f137,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f51,f134])).

fof(f134,plain,
    ( spl3_10
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f51,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f132,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f112,f105,f129])).

fof(f105,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f107,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f127,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f50,f124])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f122,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f100,f119])).

fof(f111,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f102,f59])).

fof(f117,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f114])).

fof(f114,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f56,f105])).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f54,f95])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f90])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:05 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.48  % (6117)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (6126)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (6117)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (6125)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f615,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f117,f122,f127,f132,f137,f158,f164,f187,f199,f204,f219,f221,f222,f251,f263,f264,f277,f287,f300,f346,f363,f403,f423,f441,f446,f470,f482,f494,f542,f554,f607,f608,f614])).
% 0.22/0.49  fof(f614,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_33 | ~spl3_40 | ~spl3_41),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f613])).
% 0.22/0.49  fof(f613,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_33 | ~spl3_40 | ~spl3_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f612,f402])).
% 0.22/0.49  fof(f402,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_40),
% 0.22/0.49    inference(avatar_component_clause,[],[f400])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    spl3_40 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.49  fof(f612,plain,(
% 0.22/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_33 | ~spl3_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f611,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f611,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_33 | ~spl3_41)),
% 0.22/0.49    inference(resolution,[],[f358,f422])).
% 0.22/0.49  fof(f422,plain,(
% 0.22/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_41),
% 0.22/0.49    inference(avatar_component_clause,[],[f420])).
% 0.22/0.49  fof(f420,plain,(
% 0.22/0.49    spl3_41 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.49  fof(f358,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | ~spl3_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f357])).
% 0.22/0.49  fof(f357,plain,(
% 0.22/0.49    spl3_33 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.49  fof(f608,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f607,plain,(
% 0.22/0.49    spl3_57 | ~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_30 | ~spl3_43 | ~spl3_47 | ~spl3_49),
% 0.22/0.49    inference(avatar_split_clause,[],[f602,f484,f458,f431,f297,f284,f274,f151,f604])).
% 0.22/0.49  fof(f604,plain,(
% 0.22/0.49    spl3_57 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl3_12 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    spl3_26 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    spl3_27 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    spl3_30 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.49  fof(f431,plain,(
% 0.22/0.49    spl3_43 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.49  fof(f458,plain,(
% 0.22/0.49    spl3_47 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.49  fof(f484,plain,(
% 0.22/0.49    spl3_49 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.49  fof(f602,plain,(
% 0.22/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_30 | ~spl3_43 | ~spl3_47 | ~spl3_49)),
% 0.22/0.49    inference(subsumption_resolution,[],[f558,f459])).
% 0.22/0.49  fof(f459,plain,(
% 0.22/0.49    v2_funct_1(k2_funct_1(sK2)) | ~spl3_47),
% 0.22/0.49    inference(avatar_component_clause,[],[f458])).
% 0.22/0.49  fof(f558,plain,(
% 0.22/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_30 | ~spl3_43 | ~spl3_49)),
% 0.22/0.49    inference(subsumption_resolution,[],[f557,f486])).
% 0.22/0.49  fof(f486,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_49),
% 0.22/0.49    inference(avatar_component_clause,[],[f484])).
% 0.22/0.49  fof(f557,plain,(
% 0.22/0.49    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_30 | ~spl3_43)),
% 0.22/0.49    inference(forward_demodulation,[],[f556,f286])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f284])).
% 0.22/0.49  fof(f556,plain,(
% 0.22/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_26 | ~spl3_27 | ~spl3_30 | ~spl3_43)),
% 0.22/0.49    inference(forward_demodulation,[],[f555,f286])).
% 0.22/0.49  fof(f555,plain,(
% 0.22/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_26 | ~spl3_30 | ~spl3_43)),
% 0.22/0.49    inference(subsumption_resolution,[],[f317,f432])).
% 0.22/0.49  fof(f432,plain,(
% 0.22/0.49    v1_funct_1(k2_funct_1(sK2)) | ~spl3_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f431])).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_26 | ~spl3_30)),
% 0.22/0.49    inference(forward_demodulation,[],[f316,f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f151])).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_26 | ~spl3_30)),
% 0.22/0.49    inference(subsumption_resolution,[],[f309,f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f274])).
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_30),
% 0.22/0.49    inference(resolution,[],[f299,f81])).
% 0.22/0.49  % (6118)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f297])).
% 0.22/0.49  fof(f554,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2 | ~spl3_13 | spl3_54),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f553])).
% 0.22/0.49  fof(f553,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_13 | spl3_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f552,f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl3_13 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f552,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f551,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f551,plain,(
% 0.22/0.49    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_54)),
% 0.22/0.49    inference(subsumption_resolution,[],[f550,f87])).
% 0.22/0.49  fof(f550,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_54),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f549])).
% 0.22/0.49  fof(f549,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_54),
% 0.22/0.49    inference(superposition,[],[f541,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.49  fof(f541,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | spl3_54),
% 0.22/0.49    inference(avatar_component_clause,[],[f539])).
% 0.22/0.49  fof(f539,plain,(
% 0.22/0.49    spl3_54 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.49  fof(f542,plain,(
% 0.22/0.49    ~spl3_54 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_43 | ~spl3_46 | spl3_47),
% 0.22/0.49    inference(avatar_split_clause,[],[f525,f458,f454,f431,f155,f90,f85,f539])).
% 0.22/0.49  fof(f454,plain,(
% 0.22/0.49    spl3_46 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.49  fof(f525,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f524,f92])).
% 0.22/0.49  fof(f524,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_13 | ~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f523,f156])).
% 0.22/0.49  fof(f523,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f522,f87])).
% 0.22/0.49  fof(f522,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f521,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.49  fof(f521,plain,(
% 0.22/0.49    ~v2_funct_1(k6_relat_1(k1_relat_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f520])).
% 0.22/0.49  fof(f520,plain,(
% 0.22/0.49    ~v2_funct_1(k6_relat_1(k1_relat_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(superposition,[],[f476,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.49  fof(f476,plain,(
% 0.22/0.49    ( ! [X1] : (~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))) ) | (~spl3_43 | ~spl3_46 | spl3_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f475,f455])).
% 0.22/0.49  fof(f455,plain,(
% 0.22/0.49    v1_relat_1(k2_funct_1(sK2)) | ~spl3_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f454])).
% 0.22/0.49  fof(f475,plain,(
% 0.22/0.49    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_43 | spl3_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f472,f432])).
% 0.22/0.49  fof(f472,plain,(
% 0.22/0.49    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | spl3_47),
% 0.22/0.49    inference(resolution,[],[f460,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.22/0.49  fof(f460,plain,(
% 0.22/0.49    ~v2_funct_1(k2_funct_1(sK2)) | spl3_47),
% 0.22/0.49    inference(avatar_component_clause,[],[f458])).
% 0.22/0.49  fof(f494,plain,(
% 0.22/0.49    k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f482,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2 | ~spl3_13 | spl3_48),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f481])).
% 0.22/0.49  fof(f481,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_13 | spl3_48)),
% 0.22/0.49    inference(subsumption_resolution,[],[f480,f156])).
% 0.22/0.49  fof(f480,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_48)),
% 0.22/0.49    inference(subsumption_resolution,[],[f479,f92])).
% 0.22/0.49  fof(f479,plain,(
% 0.22/0.49    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_48)),
% 0.22/0.49    inference(subsumption_resolution,[],[f478,f87])).
% 0.22/0.49  fof(f478,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_48),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f477])).
% 0.22/0.49  fof(f477,plain,(
% 0.22/0.49    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_48),
% 0.22/0.49    inference(superposition,[],[f463,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f463,plain,(
% 0.22/0.49    k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | spl3_48),
% 0.22/0.49    inference(avatar_component_clause,[],[f462])).
% 0.22/0.49  fof(f462,plain,(
% 0.22/0.49    spl3_48 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.49  fof(f470,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_13 | spl3_46),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f469])).
% 0.22/0.49  fof(f469,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_13 | spl3_46)),
% 0.22/0.49    inference(subsumption_resolution,[],[f468,f156])).
% 0.22/0.49  fof(f468,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | (~spl3_1 | spl3_46)),
% 0.22/0.49    inference(subsumption_resolution,[],[f466,f87])).
% 0.22/0.49  fof(f466,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_46),
% 0.22/0.49    inference(resolution,[],[f456,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f456,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(sK2)) | spl3_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f454])).
% 0.22/0.49  fof(f446,plain,(
% 0.22/0.49    spl3_44 | ~spl3_27 | ~spl3_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f418,f297,f284,f443])).
% 0.22/0.49  fof(f443,plain,(
% 0.22/0.49    spl3_44 <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.49  fof(f418,plain,(
% 0.22/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_27 | ~spl3_30)),
% 0.22/0.49    inference(forward_demodulation,[],[f304,f286])).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_30),
% 0.22/0.49    inference(resolution,[],[f299,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.49  fof(f441,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_13 | spl3_43),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f440])).
% 0.22/0.49  fof(f440,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_13 | spl3_43)),
% 0.22/0.49    inference(subsumption_resolution,[],[f439,f156])).
% 0.22/0.49  fof(f439,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | (~spl3_1 | spl3_43)),
% 0.22/0.49    inference(subsumption_resolution,[],[f436,f87])).
% 0.22/0.49  fof(f436,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_43),
% 0.22/0.49    inference(resolution,[],[f433,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f433,plain,(
% 0.22/0.49    ~v1_funct_1(k2_funct_1(sK2)) | spl3_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f431])).
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    spl3_41 | ~spl3_25 | ~spl3_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f324,f284,f260,f420])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    spl3_25 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.49  fof(f324,plain,(
% 0.22/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(superposition,[],[f261,f286])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f260])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    spl3_40 | ~spl3_14 | ~spl3_21 | ~spl3_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f389,f284,f214,f161,f400])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    spl3_21 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.49  fof(f389,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_21 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f236,f286])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_21)),
% 0.22/0.49    inference(superposition,[],[f163,f216])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f214])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f363,plain,(
% 0.22/0.49    spl3_33 | spl3_34 | ~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25 | ~spl3_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f355,f284,f260,f214,f161,f85,f360,f357])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    spl3_34 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    ( ! [X0] : (r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f354,f286])).
% 0.22/0.49  fof(f354,plain,(
% 0.22/0.49    ( ! [X0] : (r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f353,f216])).
% 0.22/0.49  fof(f353,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f352,f286])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f351,f216])).
% 0.22/0.49  fof(f351,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f350,f286])).
% 0.22/0.49  fof(f350,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f349,f216])).
% 0.22/0.49  fof(f349,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f348,f261])).
% 0.22/0.49  fof(f348,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14 | ~spl3_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f181,f216])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f173,f87])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.22/0.49  fof(f346,plain,(
% 0.22/0.49    spl3_32 | ~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25 | ~spl3_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f336,f284,f260,f214,f210,f161,f90,f85,f343])).
% 0.22/0.49  fof(f343,plain,(
% 0.22/0.49    spl3_32 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    spl3_20 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f335,f286])).
% 0.22/0.49  fof(f335,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f334,f216])).
% 0.22/0.49  fof(f334,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f333,f212])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f210])).
% 0.22/0.49  fof(f333,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f332,f216])).
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f331,f261])).
% 0.22/0.49  fof(f331,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f180,f216])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f179,f92])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f172,f87])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f81])).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f282,f260,f214,f210,f161,f90,f85,f297])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f281,f216])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f280,f212])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f279,f216])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f278,f261])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f178,f216])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f177,f92])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f171,f87])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    spl3_27 | ~spl3_13 | ~spl3_15 | ~spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f267,f256,f184,f155,f284])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    spl3_15 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    spl3_24 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.49  fof(f267,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_13 | ~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f266,f156])).
% 0.22/0.49  fof(f266,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_15 | ~spl3_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f265,f186])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f184])).
% 0.22/0.49  fof(f265,plain,(
% 0.22/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_24),
% 0.22/0.49    inference(resolution,[],[f258,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f256])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    spl3_26 | ~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f272,f260,f214,f210,f161,f90,f85,f274])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f271,f216])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_20 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f270,f212])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f269,f216])).
% 0.22/0.49  fof(f269,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f268,f261])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f176,f216])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f175,f92])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f170,f87])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f43])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    spl3_24 | ~spl3_25 | ~spl3_1 | ~spl3_14 | ~spl3_21 | spl3_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f254,f248,f214,f161,f85,f260,f256])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    spl3_23 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14 | ~spl3_21 | spl3_23)),
% 0.22/0.49    inference(forward_demodulation,[],[f253,f216])).
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14 | ~spl3_21 | spl3_23)),
% 0.22/0.49    inference(subsumption_resolution,[],[f252,f250])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f248])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14 | ~spl3_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f174,f216])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f166,f87])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(flattening,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ~spl3_23 | spl3_3 | ~spl3_4 | ~spl3_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f239,f214,f100,f95,f248])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl3_3 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl3_4 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f238,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v2_struct_0(sK1) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f237,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    l1_struct_0(sK1) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_21),
% 0.22/0.49    inference(superposition,[],[f61,f216])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    spl3_13 | ~spl3_14),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f218])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    $false | (spl3_13 | ~spl3_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f217,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (spl3_13 | ~spl3_14)),
% 0.22/0.49    inference(resolution,[],[f165,f163])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_13),
% 0.22/0.49    inference(resolution,[],[f157,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    spl3_18 | ~spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f167,f161,f201])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    spl3_18 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f75])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    ~spl3_17 | ~spl3_7 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f189,f129,f119,f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    spl3_17 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl3_7 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_7 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f188,f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f129])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~spl3_7),
% 0.22/0.49    inference(forward_demodulation,[],[f53,f121])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f119])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f18])).
% 0.22/0.49  fof(f18,conjecture,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    spl3_15 | ~spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f168,f161,f184])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.22/0.49    inference(resolution,[],[f163,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    spl3_14 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f147,f129,f124,f119,f161])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f143,f131])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f126,f121])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f124])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    spl3_12 | ~spl3_13 | ~spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f110,f90,f85,f155,f151])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f109,f87])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f92,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f134])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl3_10 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl3_9 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f105,f129])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl3_5 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.49    inference(resolution,[],[f107,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f124])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl3_7 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f111,f100,f119])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_4),
% 0.22/0.49    inference(resolution,[],[f102,f59])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f114])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f56,f105])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f55,f100])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    l1_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f54,f95])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f90])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    v2_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f85])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (6117)------------------------------
% 0.22/0.49  % (6117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (6117)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (6117)Memory used [KB]: 11001
% 0.22/0.49  % (6117)Time elapsed: 0.060 s
% 0.22/0.49  % (6117)------------------------------
% 0.22/0.49  % (6117)------------------------------
% 0.22/0.50  % (6113)Success in time 0.128 s
%------------------------------------------------------------------------------
