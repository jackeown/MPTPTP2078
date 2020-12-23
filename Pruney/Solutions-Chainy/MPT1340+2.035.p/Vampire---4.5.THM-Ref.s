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
% DateTime   : Thu Dec  3 13:14:22 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 566 expanded)
%              Number of leaves         :   69 ( 268 expanded)
%              Depth                    :    9
%              Number of atoms          :  915 (1838 expanded)
%              Number of equality atoms :  154 ( 326 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f143,f148,f157,f162,f167,f172,f178,f184,f190,f196,f202,f213,f218,f228,f243,f248,f253,f257,f264,f271,f276,f288,f294,f300,f316,f326,f331,f348,f357,f389,f415,f416,f470,f474,f492,f510,f517,f529,f553,f604,f610,f617,f621])).

fof(f621,plain,
    ( ~ spl3_9
    | ~ spl3_59
    | ~ spl3_56
    | spl3_67 ),
    inference(avatar_split_clause,[],[f619,f614,f467,f514,f128])).

fof(f128,plain,
    ( spl3_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f514,plain,
    ( spl3_59
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f467,plain,
    ( spl3_56
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f614,plain,
    ( spl3_67
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f619,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | spl3_67 ),
    inference(resolution,[],[f616,f86])).

% (22360)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f616,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_67 ),
    inference(avatar_component_clause,[],[f614])).

fof(f617,plain,
    ( ~ spl3_67
    | spl3_62
    | ~ spl3_65
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f612,f607,f601,f550,f614])).

fof(f550,plain,
    ( spl3_62
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f601,plain,
    ( spl3_65
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f607,plain,
    ( spl3_66
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f612,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_62
    | ~ spl3_65
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f611,f609])).

fof(f609,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f607])).

fof(f611,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_62
    | ~ spl3_65 ),
    inference(backward_demodulation,[],[f552,f603])).

fof(f603,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f601])).

fof(f552,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_62 ),
    inference(avatar_component_clause,[],[f550])).

fof(f610,plain,
    ( ~ spl3_55
    | ~ spl3_26
    | ~ spl3_30
    | ~ spl3_31
    | spl3_66
    | ~ spl3_22
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f605,f291,f206,f607,f273,f268,f236,f463])).

fof(f463,plain,
    ( spl3_55
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f236,plain,
    ( spl3_26
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f268,plain,
    ( spl3_30
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f273,plain,
    ( spl3_31
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f206,plain,
    ( spl3_22
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f291,plain,
    ( spl3_33
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f605,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f598,f208])).

fof(f208,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f598,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(trivial_inequality_removal,[],[f597])).

fof(f597,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(superposition,[],[f76,f293])).

fof(f293,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f291])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f604,plain,
    ( spl3_65
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_59
    | ~ spl3_56
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f599,f345,f467,f514,f128,f108,f601])).

fof(f108,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f345,plain,
    ( spl3_41
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f599,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_41 ),
    inference(trivial_inequality_removal,[],[f596])).

fof(f596,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_41 ),
    inference(superposition,[],[f76,f347])).

fof(f347,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f345])).

fof(f553,plain,
    ( ~ spl3_62
    | spl3_39
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f537,f526,f328,f550])).

fof(f328,plain,
    ( spl3_39
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f526,plain,
    ( spl3_60
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f537,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_39
    | ~ spl3_60 ),
    inference(backward_demodulation,[],[f330,f528])).

fof(f528,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f526])).

fof(f330,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_39 ),
    inference(avatar_component_clause,[],[f328])).

fof(f529,plain,
    ( ~ spl3_56
    | spl3_49
    | spl3_60
    | ~ spl3_57
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f524,f514,f489,f526,f408,f467])).

fof(f408,plain,
    ( spl3_49
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f489,plain,
    ( spl3_57
  <=> k2_struct_0(sK0) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f524,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_57
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f518,f491])).

fof(f491,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f489])).

fof(f518,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_59 ),
    inference(resolution,[],[f516,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f516,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f514])).

fof(f517,plain,
    ( ~ spl3_31
    | ~ spl3_30
    | spl3_59
    | ~ spl3_33
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f512,f508,f291,f514,f268,f273])).

fof(f508,plain,
    ( spl3_58
  <=> ! [X1,X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(sK2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f512,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_33
    | ~ spl3_58 ),
    inference(trivial_inequality_removal,[],[f511])).

fof(f511,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_33
    | ~ spl3_58 ),
    inference(superposition,[],[f509,f293])).

fof(f509,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(sK2),X1,X0) )
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f508])).

fof(f510,plain,
    ( ~ spl3_26
    | ~ spl3_55
    | spl3_58
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f506,f206,f508,f463,f236])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_22 ),
    inference(superposition,[],[f75,f208])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f492,plain,
    ( ~ spl3_23
    | spl3_57
    | ~ spl3_9
    | ~ spl3_42
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f487,f412,f355,f128,f489,f210])).

fof(f210,plain,
    ( spl3_23
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f355,plain,
    ( spl3_42
  <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f412,plain,
    ( spl3_50
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f487,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_9
    | ~ spl3_42
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f486,f414])).

fof(f414,plain,
    ( k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f412])).

fof(f486,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_9
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f483,f356])).

fof(f356,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f355])).

fof(f483,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f376,f130])).

fof(f130,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f376,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,k2_relat_1(X0)) = k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f474,plain,
    ( ~ spl3_23
    | ~ spl3_5
    | ~ spl3_9
    | spl3_55 ),
    inference(avatar_split_clause,[],[f472,f463,f128,f108,f210])).

fof(f472,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_55 ),
    inference(resolution,[],[f465,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f465,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_55 ),
    inference(avatar_component_clause,[],[f463])).

fof(f470,plain,
    ( ~ spl3_26
    | ~ spl3_55
    | ~ spl3_30
    | ~ spl3_31
    | spl3_56
    | ~ spl3_22
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f461,f291,f206,f467,f273,f268,f463,f236])).

fof(f461,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f454,f208])).

fof(f454,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(superposition,[],[f74,f293])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f416,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f415,plain,
    ( ~ spl3_38
    | spl3_49
    | spl3_50
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f406,f386,f313,f412,f408,f323])).

fof(f323,plain,
    ( spl3_38
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f313,plain,
    ( spl3_36
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f386,plain,
    ( spl3_46
  <=> k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f406,plain,
    ( k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f395,f388])).

fof(f388,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f386])).

fof(f395,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_36 ),
    inference(resolution,[],[f72,f315])).

fof(f315,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f313])).

fof(f389,plain,
    ( spl3_46
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f384,f313,f386])).

fof(f384,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f377,f340])).

fof(f340,plain,
    ( ! [X3] : k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X3) = k10_relat_1(sK2,X3)
    | ~ spl3_36 ),
    inference(resolution,[],[f77,f315])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f377,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_36 ),
    inference(resolution,[],[f66,f315])).

fof(f357,plain,
    ( ~ spl3_23
    | spl3_42
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f351,f128,f355,f210])).

fof(f351,plain,
    ( ! [X0] :
        ( k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_9 ),
    inference(resolution,[],[f339,f130])).

fof(f339,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k8_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1,X2) = k10_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f77,f59])).

fof(f348,plain,
    ( ~ spl3_23
    | spl3_41
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f341,f128,f345,f210])).

fof(f341,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f282,f130])).

fof(f282,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(X0) = k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f64,f59])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
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

fof(f331,plain,
    ( ~ spl3_39
    | spl3_20
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f305,f297,f193,f328])).

fof(f193,plain,
    ( spl3_20
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f297,plain,
    ( spl3_34
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f305,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_20
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f195,f299])).

fof(f299,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f297])).

fof(f195,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f326,plain,
    ( spl3_38
    | ~ spl3_17
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f304,f297,f175,f323])).

fof(f175,plain,
    ( spl3_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f304,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_17
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f177,f299])).

fof(f177,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f316,plain,
    ( spl3_36
    | ~ spl3_18
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f302,f297,f181,f313])).

fof(f181,plain,
    ( spl3_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_18
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f183,f299])).

fof(f183,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f300,plain,
    ( spl3_34
    | ~ spl3_19
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f295,f285,f187,f297])).

fof(f187,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f285,plain,
    ( spl3_32
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f295,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f189,f287])).

fof(f287,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f285])).

fof(f189,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f294,plain,
    ( spl3_33
    | ~ spl3_29
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f289,f268,f261,f291])).

fof(f261,plain,
    ( spl3_29
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f289,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_29
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f283,f263])).

fof(f263,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f261])).

fof(f283,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(resolution,[],[f64,f270])).

fof(f270,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f288,plain,
    ( spl3_32
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f281,f181,f285])).

fof(f281,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f64,f183])).

fof(f276,plain,
    ( spl3_31
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f266,f261,f245,f273])).

fof(f245,plain,
    ( spl3_28
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f266,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f247,f263])).

fof(f247,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f245])).

fof(f271,plain,
    ( spl3_30
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f265,f261,f240,f268])).

fof(f240,plain,
    ( spl3_27
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f265,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f242,f263])).

fof(f242,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f264,plain,
    ( spl3_29
    | ~ spl3_23
    | ~ spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f258,f108,f128,f210,f261])).

fof(f258,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f62,f110])).

fof(f110,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f257,plain,
    ( ~ spl3_23
    | ~ spl3_5
    | ~ spl3_9
    | spl3_26 ),
    inference(avatar_split_clause,[],[f255,f236,f128,f108,f210])).

fof(f255,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_26 ),
    inference(resolution,[],[f238,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f238,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f253,plain,
    ( ~ spl3_23
    | ~ spl3_5
    | ~ spl3_9
    | spl3_25 ),
    inference(avatar_split_clause,[],[f250,f232,f128,f108,f210])).

% (22340)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f232,plain,
    ( spl3_25
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f250,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_25 ),
    inference(resolution,[],[f234,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f234,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f248,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | spl3_28
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f230,f225,f245,f236,f232])).

fof(f225,plain,
    ( spl3_24
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f230,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(superposition,[],[f58,f227])).

fof(f227,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f243,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | spl3_27
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f229,f225,f240,f236,f232])).

fof(f229,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(superposition,[],[f59,f227])).

fof(f228,plain,
    ( spl3_24
    | ~ spl3_23
    | ~ spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f222,f108,f128,f210,f225])).

fof(f222,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f61,f110])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f218,plain,
    ( ~ spl3_18
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl3_18
    | spl3_23 ),
    inference(subsumption_resolution,[],[f183,f215])).

fof(f215,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_23 ),
    inference(resolution,[],[f212,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f212,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f213,plain,
    ( spl3_22
    | ~ spl3_23
    | ~ spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f203,f108,f128,f210,f206])).

fof(f203,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f60,f110])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f202,plain,
    ( ~ spl3_21
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f197,f98,f93,f199])).

fof(f199,plain,
    ( spl3_21
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f93,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f197,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3 ),
    inference(resolution,[],[f54,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f54,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f196,plain,
    ( ~ spl3_20
    | ~ spl3_11
    | spl3_13 ),
    inference(avatar_split_clause,[],[f191,f154,f140,f193])).

fof(f140,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f154,plain,
    ( spl3_13
  <=> r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f191,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_11
    | spl3_13 ),
    inference(forward_demodulation,[],[f156,f142])).

fof(f142,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f156,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f190,plain,
    ( spl3_19
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f185,f159,f140,f187])).

fof(f159,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f185,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f161,f142])).

fof(f161,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f184,plain,
    ( spl3_18
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f179,f164,f140,f181])).

fof(f164,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f179,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f166,f142])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f178,plain,
    ( spl3_17
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f173,f169,f140,f175])).

fof(f169,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f173,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f171,f142])).

fof(f171,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f172,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f152,f145,f123,f169])).

fof(f123,plain,
    ( spl3_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f145,plain,
    ( spl3_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f152,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f125,f147])).

fof(f147,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f125,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f167,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f151,f145,f118,f164])).

fof(f118,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f120,f147])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f162,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f150,f145,f113,f159])).

fof(f113,plain,
    ( spl3_6
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f150,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f115,f147])).

fof(f115,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f157,plain,
    ( ~ spl3_13
    | spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f149,f145,f103,f154])).

fof(f103,plain,
    ( spl3_4
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f149,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f105,f147])).

fof(f105,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f148,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f138,f93,f145])).

fof(f138,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f95])).

fof(f95,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f143,plain,
    ( spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f137,f88,f140])).

fof(f88,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f137,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f53,f90])).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f136,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f52,f133])).

fof(f133,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f43,f128])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f126,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f44,f123])).

fof(f44,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f121,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f113])).

fof(f46,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f48,f103])).

fof(f48,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (22336)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (22358)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (22350)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (22335)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (22353)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (22342)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (22339)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (22346)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (22352)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (22338)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.24/0.52  % (22343)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.24/0.52  % (22335)Refutation not found, incomplete strategy% (22335)------------------------------
% 1.24/0.52  % (22335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (22335)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (22335)Memory used [KB]: 10746
% 1.24/0.52  % (22335)Time elapsed: 0.093 s
% 1.24/0.52  % (22335)------------------------------
% 1.24/0.52  % (22335)------------------------------
% 1.24/0.52  % (22344)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.24/0.52  % (22337)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.24/0.52  % (22347)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.24/0.52  % (22357)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.24/0.52  % (22350)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.53  % (22345)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.24/0.53  % (22349)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.24/0.53  % (22355)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.24/0.53  % (22354)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.24/0.53  % (22342)Refutation not found, incomplete strategy% (22342)------------------------------
% 1.24/0.53  % (22342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (22342)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (22342)Memory used [KB]: 1791
% 1.24/0.53  % (22342)Time elapsed: 0.063 s
% 1.24/0.53  % (22342)------------------------------
% 1.24/0.53  % (22342)------------------------------
% 1.38/0.53  % SZS output start Proof for theBenchmark
% 1.38/0.53  fof(f622,plain,(
% 1.38/0.53    $false),
% 1.38/0.53    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f143,f148,f157,f162,f167,f172,f178,f184,f190,f196,f202,f213,f218,f228,f243,f248,f253,f257,f264,f271,f276,f288,f294,f300,f316,f326,f331,f348,f357,f389,f415,f416,f470,f474,f492,f510,f517,f529,f553,f604,f610,f617,f621])).
% 1.38/0.53  fof(f621,plain,(
% 1.38/0.53    ~spl3_9 | ~spl3_59 | ~spl3_56 | spl3_67),
% 1.38/0.53    inference(avatar_split_clause,[],[f619,f614,f467,f514,f128])).
% 1.38/0.53  fof(f128,plain,(
% 1.38/0.53    spl3_9 <=> v1_funct_1(sK2)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.38/0.54  fof(f514,plain,(
% 1.38/0.54    spl3_59 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.38/0.54  fof(f467,plain,(
% 1.38/0.54    spl3_56 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.38/0.54  fof(f614,plain,(
% 1.38/0.54    spl3_67 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 1.38/0.54  fof(f619,plain,(
% 1.38/0.54    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | spl3_67),
% 1.38/0.54    inference(resolution,[],[f616,f86])).
% 1.38/0.54  % (22360)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.38/0.54  fof(f86,plain,(
% 1.38/0.54    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f85])).
% 1.38/0.54  fof(f85,plain,(
% 1.38/0.54    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.38/0.54    inference(equality_resolution,[],[f78])).
% 1.38/0.54  fof(f78,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f42])).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.54    inference(flattening,[],[f41])).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.54    inference(ennf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.38/0.54  fof(f616,plain,(
% 1.38/0.54    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_67),
% 1.38/0.54    inference(avatar_component_clause,[],[f614])).
% 1.38/0.54  fof(f617,plain,(
% 1.38/0.54    ~spl3_67 | spl3_62 | ~spl3_65 | ~spl3_66),
% 1.38/0.54    inference(avatar_split_clause,[],[f612,f607,f601,f550,f614])).
% 1.38/0.54  fof(f550,plain,(
% 1.38/0.54    spl3_62 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.38/0.54  fof(f601,plain,(
% 1.38/0.54    spl3_65 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.38/0.54  fof(f607,plain,(
% 1.38/0.54    spl3_66 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 1.38/0.54  fof(f612,plain,(
% 1.38/0.54    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (spl3_62 | ~spl3_65 | ~spl3_66)),
% 1.38/0.54    inference(forward_demodulation,[],[f611,f609])).
% 1.38/0.54  fof(f609,plain,(
% 1.38/0.54    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_66),
% 1.38/0.54    inference(avatar_component_clause,[],[f607])).
% 1.38/0.54  fof(f611,plain,(
% 1.38/0.54    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (spl3_62 | ~spl3_65)),
% 1.38/0.54    inference(backward_demodulation,[],[f552,f603])).
% 1.38/0.54  fof(f603,plain,(
% 1.38/0.54    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_65),
% 1.38/0.54    inference(avatar_component_clause,[],[f601])).
% 1.38/0.54  fof(f552,plain,(
% 1.38/0.54    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_62),
% 1.38/0.54    inference(avatar_component_clause,[],[f550])).
% 1.38/0.54  fof(f610,plain,(
% 1.38/0.54    ~spl3_55 | ~spl3_26 | ~spl3_30 | ~spl3_31 | spl3_66 | ~spl3_22 | ~spl3_33),
% 1.38/0.54    inference(avatar_split_clause,[],[f605,f291,f206,f607,f273,f268,f236,f463])).
% 1.38/0.54  fof(f463,plain,(
% 1.38/0.54    spl3_55 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 1.38/0.54  fof(f236,plain,(
% 1.38/0.54    spl3_26 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.38/0.54  fof(f268,plain,(
% 1.38/0.54    spl3_30 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.38/0.54  fof(f273,plain,(
% 1.38/0.54    spl3_31 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.38/0.54  fof(f206,plain,(
% 1.38/0.54    spl3_22 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.38/0.54  fof(f291,plain,(
% 1.38/0.54    spl3_33 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.38/0.54  fof(f605,plain,(
% 1.38/0.54    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_22 | ~spl3_33)),
% 1.38/0.54    inference(forward_demodulation,[],[f598,f208])).
% 1.38/0.54  fof(f208,plain,(
% 1.38/0.54    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_22),
% 1.38/0.54    inference(avatar_component_clause,[],[f206])).
% 1.38/0.54  fof(f598,plain,(
% 1.38/0.54    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_33),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f597])).
% 1.38/0.54  fof(f597,plain,(
% 1.38/0.54    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_33),
% 1.38/0.54    inference(superposition,[],[f76,f293])).
% 1.38/0.54  fof(f293,plain,(
% 1.38/0.54    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_33),
% 1.38/0.54    inference(avatar_component_clause,[],[f291])).
% 1.38/0.54  fof(f76,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.54    inference(flattening,[],[f38])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.54    inference(ennf_transformation,[],[f15])).
% 1.38/0.54  fof(f15,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.38/0.54  fof(f604,plain,(
% 1.38/0.54    spl3_65 | ~spl3_5 | ~spl3_9 | ~spl3_59 | ~spl3_56 | ~spl3_41),
% 1.38/0.54    inference(avatar_split_clause,[],[f599,f345,f467,f514,f128,f108,f601])).
% 1.38/0.54  fof(f108,plain,(
% 1.38/0.54    spl3_5 <=> v2_funct_1(sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.38/0.54  fof(f345,plain,(
% 1.38/0.54    spl3_41 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.38/0.54  fof(f599,plain,(
% 1.38/0.54    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_41),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f596])).
% 1.38/0.54  fof(f596,plain,(
% 1.38/0.54    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_41),
% 1.38/0.54    inference(superposition,[],[f76,f347])).
% 1.38/0.54  fof(f347,plain,(
% 1.38/0.54    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_41),
% 1.38/0.54    inference(avatar_component_clause,[],[f345])).
% 1.38/0.54  fof(f553,plain,(
% 1.38/0.54    ~spl3_62 | spl3_39 | ~spl3_60),
% 1.38/0.54    inference(avatar_split_clause,[],[f537,f526,f328,f550])).
% 1.38/0.54  fof(f328,plain,(
% 1.38/0.54    spl3_39 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.38/0.54  fof(f526,plain,(
% 1.38/0.54    spl3_60 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.38/0.54  fof(f537,plain,(
% 1.38/0.54    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_39 | ~spl3_60)),
% 1.38/0.54    inference(backward_demodulation,[],[f330,f528])).
% 1.38/0.54  fof(f528,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_60),
% 1.38/0.54    inference(avatar_component_clause,[],[f526])).
% 1.38/0.54  fof(f330,plain,(
% 1.38/0.54    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | spl3_39),
% 1.38/0.54    inference(avatar_component_clause,[],[f328])).
% 1.38/0.54  fof(f529,plain,(
% 1.38/0.54    ~spl3_56 | spl3_49 | spl3_60 | ~spl3_57 | ~spl3_59),
% 1.38/0.54    inference(avatar_split_clause,[],[f524,f514,f489,f526,f408,f467])).
% 1.38/0.54  fof(f408,plain,(
% 1.38/0.54    spl3_49 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.38/0.54  fof(f489,plain,(
% 1.38/0.54    spl3_57 <=> k2_struct_0(sK0) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.38/0.54  fof(f524,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_57 | ~spl3_59)),
% 1.38/0.54    inference(forward_demodulation,[],[f518,f491])).
% 1.38/0.54  fof(f491,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_57),
% 1.38/0.54    inference(avatar_component_clause,[],[f489])).
% 1.38/0.54  fof(f518,plain,(
% 1.38/0.54    k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_59),
% 1.38/0.54    inference(resolution,[],[f516,f72])).
% 1.38/0.54  fof(f72,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(flattening,[],[f34])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.38/0.54  fof(f516,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_59),
% 1.38/0.54    inference(avatar_component_clause,[],[f514])).
% 1.38/0.54  fof(f517,plain,(
% 1.38/0.54    ~spl3_31 | ~spl3_30 | spl3_59 | ~spl3_33 | ~spl3_58),
% 1.38/0.54    inference(avatar_split_clause,[],[f512,f508,f291,f514,f268,f273])).
% 1.38/0.54  fof(f508,plain,(
% 1.38/0.54    spl3_58 <=> ! [X1,X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(sK2),X1,X0))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.38/0.54  fof(f512,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_33 | ~spl3_58)),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f511])).
% 1.38/0.54  fof(f511,plain,(
% 1.38/0.54    k1_relat_1(sK2) != k1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_33 | ~spl3_58)),
% 1.38/0.54    inference(superposition,[],[f509,f293])).
% 1.38/0.54  fof(f509,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(sK2),X1,X0)) ) | ~spl3_58),
% 1.38/0.54    inference(avatar_component_clause,[],[f508])).
% 1.38/0.54  fof(f510,plain,(
% 1.38/0.54    ~spl3_26 | ~spl3_55 | spl3_58 | ~spl3_22),
% 1.38/0.54    inference(avatar_split_clause,[],[f506,f206,f508,f463,f236])).
% 1.38/0.54  fof(f506,plain,(
% 1.38/0.54    ( ! [X0,X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(k2_funct_1(sK2),X1,X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(k2_funct_1(sK2)) | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl3_22),
% 1.38/0.54    inference(superposition,[],[f75,f208])).
% 1.38/0.54  fof(f75,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.54    inference(flattening,[],[f36])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.38/0.54  fof(f492,plain,(
% 1.38/0.54    ~spl3_23 | spl3_57 | ~spl3_9 | ~spl3_42 | ~spl3_50),
% 1.38/0.54    inference(avatar_split_clause,[],[f487,f412,f355,f128,f489,f210])).
% 1.38/0.54  fof(f210,plain,(
% 1.38/0.54    spl3_23 <=> v1_relat_1(sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.38/0.54  fof(f355,plain,(
% 1.38/0.54    spl3_42 <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.38/0.54  fof(f412,plain,(
% 1.38/0.54    spl3_50 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.38/0.54  fof(f487,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_relat_1(sK2) | (~spl3_9 | ~spl3_42 | ~spl3_50)),
% 1.38/0.54    inference(forward_demodulation,[],[f486,f414])).
% 1.38/0.54  fof(f414,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_50),
% 1.38/0.54    inference(avatar_component_clause,[],[f412])).
% 1.38/0.54  fof(f486,plain,(
% 1.38/0.54    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_relat_1(sK2) | (~spl3_9 | ~spl3_42)),
% 1.38/0.54    inference(forward_demodulation,[],[f483,f356])).
% 1.38/0.54  fof(f356,plain,(
% 1.38/0.54    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)) ) | ~spl3_42),
% 1.38/0.54    inference(avatar_component_clause,[],[f355])).
% 1.38/0.54  fof(f483,plain,(
% 1.38/0.54    k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_9),
% 1.38/0.54    inference(resolution,[],[f376,f130])).
% 1.38/0.54  fof(f130,plain,(
% 1.38/0.54    v1_funct_1(sK2) | ~spl3_9),
% 1.38/0.54    inference(avatar_component_clause,[],[f128])).
% 1.38/0.54  fof(f376,plain,(
% 1.38/0.54    ( ! [X0] : (~v1_funct_1(X0) | k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,k2_relat_1(X0)) = k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(resolution,[],[f66,f59])).
% 1.38/0.54  fof(f59,plain,(
% 1.38/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.54    inference(flattening,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.38/0.54  fof(f474,plain,(
% 1.38/0.54    ~spl3_23 | ~spl3_5 | ~spl3_9 | spl3_55),
% 1.38/0.54    inference(avatar_split_clause,[],[f472,f463,f128,f108,f210])).
% 1.38/0.54  fof(f472,plain,(
% 1.38/0.54    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_55),
% 1.38/0.54    inference(resolution,[],[f465,f57])).
% 1.38/0.54  fof(f57,plain,(
% 1.38/0.54    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.54    inference(flattening,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.38/0.54  fof(f465,plain,(
% 1.38/0.54    ~v2_funct_1(k2_funct_1(sK2)) | spl3_55),
% 1.38/0.54    inference(avatar_component_clause,[],[f463])).
% 1.38/0.54  fof(f470,plain,(
% 1.38/0.54    ~spl3_26 | ~spl3_55 | ~spl3_30 | ~spl3_31 | spl3_56 | ~spl3_22 | ~spl3_33),
% 1.38/0.54    inference(avatar_split_clause,[],[f461,f291,f206,f467,f273,f268,f463,f236])).
% 1.38/0.54  fof(f461,plain,(
% 1.38/0.54    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_22 | ~spl3_33)),
% 1.38/0.54    inference(forward_demodulation,[],[f454,f208])).
% 1.38/0.54  fof(f454,plain,(
% 1.38/0.54    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_33),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f451])).
% 1.38/0.54  fof(f451,plain,(
% 1.38/0.54    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_33),
% 1.38/0.54    inference(superposition,[],[f74,f293])).
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f416,plain,(
% 1.38/0.54    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k1_xboole_0 != k2_relat_1(sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 1.38/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.38/0.54  fof(f415,plain,(
% 1.38/0.54    ~spl3_38 | spl3_49 | spl3_50 | ~spl3_36 | ~spl3_46),
% 1.38/0.54    inference(avatar_split_clause,[],[f406,f386,f313,f412,f408,f323])).
% 1.38/0.54  fof(f323,plain,(
% 1.38/0.54    spl3_38 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.38/0.54  fof(f313,plain,(
% 1.38/0.54    spl3_36 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.38/0.54  fof(f386,plain,(
% 1.38/0.54    spl3_46 <=> k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.38/0.54  fof(f406,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_36 | ~spl3_46)),
% 1.38/0.54    inference(forward_demodulation,[],[f395,f388])).
% 1.38/0.54  fof(f388,plain,(
% 1.38/0.54    k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_46),
% 1.38/0.54    inference(avatar_component_clause,[],[f386])).
% 1.38/0.54  fof(f395,plain,(
% 1.38/0.54    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_36),
% 1.38/0.54    inference(resolution,[],[f72,f315])).
% 1.38/0.54  fof(f315,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_36),
% 1.38/0.54    inference(avatar_component_clause,[],[f313])).
% 1.38/0.54  fof(f389,plain,(
% 1.38/0.54    spl3_46 | ~spl3_36),
% 1.38/0.54    inference(avatar_split_clause,[],[f384,f313,f386])).
% 1.38/0.54  fof(f384,plain,(
% 1.38/0.54    k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_36),
% 1.38/0.54    inference(forward_demodulation,[],[f377,f340])).
% 1.38/0.54  fof(f340,plain,(
% 1.38/0.54    ( ! [X3] : (k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X3) = k10_relat_1(sK2,X3)) ) | ~spl3_36),
% 1.38/0.54    inference(resolution,[],[f77,f315])).
% 1.38/0.54  fof(f77,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.38/0.54  fof(f377,plain,(
% 1.38/0.54    k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_36),
% 1.38/0.54    inference(resolution,[],[f66,f315])).
% 1.38/0.54  fof(f357,plain,(
% 1.38/0.54    ~spl3_23 | spl3_42 | ~spl3_9),
% 1.38/0.54    inference(avatar_split_clause,[],[f351,f128,f355,f210])).
% 1.38/0.54  fof(f351,plain,(
% 1.38/0.54    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_9),
% 1.38/0.54    inference(resolution,[],[f339,f130])).
% 1.38/0.54  fof(f339,plain,(
% 1.38/0.54    ( ! [X2,X1] : (~v1_funct_1(X1) | k8_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1,X2) = k10_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 1.38/0.54    inference(resolution,[],[f77,f59])).
% 1.38/0.54  fof(f348,plain,(
% 1.38/0.54    ~spl3_23 | spl3_41 | ~spl3_9),
% 1.38/0.54    inference(avatar_split_clause,[],[f341,f128,f345,f210])).
% 1.38/0.54  fof(f341,plain,(
% 1.38/0.54    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_relat_1(sK2) | ~spl3_9),
% 1.38/0.54    inference(resolution,[],[f282,f130])).
% 1.38/0.54  fof(f282,plain,(
% 1.38/0.54    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) = k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(resolution,[],[f64,f59])).
% 1.38/0.54  fof(f64,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f32])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.38/0.54  fof(f331,plain,(
% 1.38/0.54    ~spl3_39 | spl3_20 | ~spl3_34),
% 1.38/0.54    inference(avatar_split_clause,[],[f305,f297,f193,f328])).
% 1.38/0.54  fof(f193,plain,(
% 1.38/0.54    spl3_20 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.38/0.54  fof(f297,plain,(
% 1.38/0.54    spl3_34 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.38/0.54  fof(f305,plain,(
% 1.38/0.54    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | (spl3_20 | ~spl3_34)),
% 1.38/0.54    inference(backward_demodulation,[],[f195,f299])).
% 1.38/0.54  fof(f299,plain,(
% 1.38/0.54    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_34),
% 1.38/0.54    inference(avatar_component_clause,[],[f297])).
% 1.38/0.54  fof(f195,plain,(
% 1.38/0.54    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_20),
% 1.38/0.54    inference(avatar_component_clause,[],[f193])).
% 1.38/0.54  fof(f326,plain,(
% 1.38/0.54    spl3_38 | ~spl3_17 | ~spl3_34),
% 1.38/0.54    inference(avatar_split_clause,[],[f304,f297,f175,f323])).
% 1.38/0.54  fof(f175,plain,(
% 1.38/0.54    spl3_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.38/0.54  fof(f304,plain,(
% 1.38/0.54    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_17 | ~spl3_34)),
% 1.38/0.54    inference(backward_demodulation,[],[f177,f299])).
% 1.38/0.54  fof(f177,plain,(
% 1.38/0.54    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_17),
% 1.38/0.54    inference(avatar_component_clause,[],[f175])).
% 1.38/0.54  fof(f316,plain,(
% 1.38/0.54    spl3_36 | ~spl3_18 | ~spl3_34),
% 1.38/0.54    inference(avatar_split_clause,[],[f302,f297,f181,f313])).
% 1.38/0.54  fof(f181,plain,(
% 1.38/0.54    spl3_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.38/0.54  fof(f302,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_18 | ~spl3_34)),
% 1.38/0.54    inference(backward_demodulation,[],[f183,f299])).
% 1.38/0.54  fof(f183,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_18),
% 1.38/0.54    inference(avatar_component_clause,[],[f181])).
% 1.38/0.54  fof(f300,plain,(
% 1.38/0.54    spl3_34 | ~spl3_19 | ~spl3_32),
% 1.38/0.54    inference(avatar_split_clause,[],[f295,f285,f187,f297])).
% 1.38/0.54  fof(f187,plain,(
% 1.38/0.54    spl3_19 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.38/0.54  fof(f285,plain,(
% 1.38/0.54    spl3_32 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.38/0.54  fof(f295,plain,(
% 1.38/0.54    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_19 | ~spl3_32)),
% 1.38/0.54    inference(backward_demodulation,[],[f189,f287])).
% 1.38/0.54  fof(f287,plain,(
% 1.38/0.54    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_32),
% 1.38/0.54    inference(avatar_component_clause,[],[f285])).
% 1.38/0.54  fof(f189,plain,(
% 1.38/0.54    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_19),
% 1.38/0.54    inference(avatar_component_clause,[],[f187])).
% 1.38/0.54  fof(f294,plain,(
% 1.38/0.54    spl3_33 | ~spl3_29 | ~spl3_30),
% 1.38/0.54    inference(avatar_split_clause,[],[f289,f268,f261,f291])).
% 1.38/0.54  fof(f261,plain,(
% 1.38/0.54    spl3_29 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.38/0.54  fof(f289,plain,(
% 1.38/0.54    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_29 | ~spl3_30)),
% 1.38/0.54    inference(forward_demodulation,[],[f283,f263])).
% 1.38/0.54  fof(f263,plain,(
% 1.38/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_29),
% 1.38/0.54    inference(avatar_component_clause,[],[f261])).
% 1.38/0.54  fof(f283,plain,(
% 1.38/0.54    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_30),
% 1.38/0.54    inference(resolution,[],[f64,f270])).
% 1.38/0.54  fof(f270,plain,(
% 1.38/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_30),
% 1.38/0.54    inference(avatar_component_clause,[],[f268])).
% 1.38/0.54  fof(f288,plain,(
% 1.38/0.54    spl3_32 | ~spl3_18),
% 1.38/0.54    inference(avatar_split_clause,[],[f281,f181,f285])).
% 1.38/0.54  fof(f281,plain,(
% 1.38/0.54    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_18),
% 1.38/0.54    inference(resolution,[],[f64,f183])).
% 1.38/0.54  fof(f276,plain,(
% 1.38/0.54    spl3_31 | ~spl3_28 | ~spl3_29),
% 1.38/0.54    inference(avatar_split_clause,[],[f266,f261,f245,f273])).
% 1.38/0.54  fof(f245,plain,(
% 1.38/0.54    spl3_28 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.38/0.54  fof(f266,plain,(
% 1.38/0.54    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_28 | ~spl3_29)),
% 1.38/0.54    inference(backward_demodulation,[],[f247,f263])).
% 1.38/0.54  fof(f247,plain,(
% 1.38/0.54    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl3_28),
% 1.38/0.54    inference(avatar_component_clause,[],[f245])).
% 1.38/0.54  fof(f271,plain,(
% 1.38/0.54    spl3_30 | ~spl3_27 | ~spl3_29),
% 1.38/0.54    inference(avatar_split_clause,[],[f265,f261,f240,f268])).
% 1.38/0.54  fof(f240,plain,(
% 1.38/0.54    spl3_27 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.38/0.54  fof(f265,plain,(
% 1.38/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_27 | ~spl3_29)),
% 1.38/0.54    inference(backward_demodulation,[],[f242,f263])).
% 1.38/0.54  fof(f242,plain,(
% 1.38/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_27),
% 1.38/0.54    inference(avatar_component_clause,[],[f240])).
% 1.38/0.54  fof(f264,plain,(
% 1.38/0.54    spl3_29 | ~spl3_23 | ~spl3_9 | ~spl3_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f258,f108,f128,f210,f261])).
% 1.38/0.54  fof(f258,plain,(
% 1.38/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f62,f110])).
% 1.38/0.54  fof(f110,plain,(
% 1.38/0.54    v2_funct_1(sK2) | ~spl3_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f108])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f30])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.54    inference(flattening,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.38/0.54  fof(f257,plain,(
% 1.38/0.54    ~spl3_23 | ~spl3_5 | ~spl3_9 | spl3_26),
% 1.38/0.54    inference(avatar_split_clause,[],[f255,f236,f128,f108,f210])).
% 1.38/0.54  fof(f255,plain,(
% 1.38/0.54    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_26),
% 1.38/0.54    inference(resolution,[],[f238,f56])).
% 1.38/0.54  fof(f56,plain,(
% 1.38/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f24])).
% 1.38/0.54  fof(f238,plain,(
% 1.38/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_26),
% 1.38/0.54    inference(avatar_component_clause,[],[f236])).
% 1.38/0.54  fof(f253,plain,(
% 1.38/0.54    ~spl3_23 | ~spl3_5 | ~spl3_9 | spl3_25),
% 1.38/0.54    inference(avatar_split_clause,[],[f250,f232,f128,f108,f210])).
% 1.38/0.54  % (22340)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.38/0.54  fof(f232,plain,(
% 1.38/0.54    spl3_25 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.38/0.54  fof(f250,plain,(
% 1.38/0.54    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_25),
% 1.38/0.54    inference(resolution,[],[f234,f55])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f24])).
% 1.38/0.54  fof(f234,plain,(
% 1.38/0.54    ~v1_relat_1(k2_funct_1(sK2)) | spl3_25),
% 1.38/0.54    inference(avatar_component_clause,[],[f232])).
% 1.38/0.54  fof(f248,plain,(
% 1.38/0.54    ~spl3_25 | ~spl3_26 | spl3_28 | ~spl3_24),
% 1.38/0.54    inference(avatar_split_clause,[],[f230,f225,f245,f236,f232])).
% 1.38/0.54  fof(f225,plain,(
% 1.38/0.54    spl3_24 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.38/0.54  fof(f230,plain,(
% 1.38/0.54    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 1.38/0.54    inference(superposition,[],[f58,f227])).
% 1.38/0.54  fof(f227,plain,(
% 1.38/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 1.38/0.54    inference(avatar_component_clause,[],[f225])).
% 1.38/0.54  fof(f58,plain,(
% 1.38/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f26])).
% 1.38/0.54  fof(f243,plain,(
% 1.38/0.54    ~spl3_25 | ~spl3_26 | spl3_27 | ~spl3_24),
% 1.38/0.54    inference(avatar_split_clause,[],[f229,f225,f240,f236,f232])).
% 1.38/0.54  fof(f229,plain,(
% 1.38/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 1.38/0.54    inference(superposition,[],[f59,f227])).
% 1.38/0.54  fof(f228,plain,(
% 1.38/0.54    spl3_24 | ~spl3_23 | ~spl3_9 | ~spl3_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f222,f108,f128,f210,f225])).
% 1.38/0.54  fof(f222,plain,(
% 1.38/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f61,f110])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f30])).
% 1.38/0.54  fof(f218,plain,(
% 1.38/0.54    ~spl3_18 | spl3_23),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f217])).
% 1.38/0.54  fof(f217,plain,(
% 1.38/0.54    $false | (~spl3_18 | spl3_23)),
% 1.38/0.54    inference(subsumption_resolution,[],[f183,f215])).
% 1.38/0.54  fof(f215,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_23),
% 1.38/0.54    inference(resolution,[],[f212,f63])).
% 1.38/0.54  fof(f63,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.54    inference(ennf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.54  fof(f212,plain,(
% 1.38/0.54    ~v1_relat_1(sK2) | spl3_23),
% 1.38/0.54    inference(avatar_component_clause,[],[f210])).
% 1.38/0.54  fof(f213,plain,(
% 1.38/0.54    spl3_22 | ~spl3_23 | ~spl3_9 | ~spl3_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f203,f108,f128,f210,f206])).
% 1.38/0.54  fof(f203,plain,(
% 1.38/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f60,f110])).
% 1.38/0.54  fof(f60,plain,(
% 1.38/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.54    inference(flattening,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.38/0.54  fof(f202,plain,(
% 1.38/0.54    ~spl3_21 | ~spl3_2 | spl3_3),
% 1.38/0.54    inference(avatar_split_clause,[],[f197,f98,f93,f199])).
% 1.38/0.54  fof(f199,plain,(
% 1.38/0.54    spl3_21 <=> v1_xboole_0(k2_struct_0(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.38/0.54  fof(f93,plain,(
% 1.38/0.54    spl3_2 <=> l1_struct_0(sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.38/0.54  fof(f98,plain,(
% 1.38/0.54    spl3_3 <=> v2_struct_0(sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.38/0.54  fof(f197,plain,(
% 1.38/0.54    ~l1_struct_0(sK1) | ~v1_xboole_0(k2_struct_0(sK1)) | spl3_3),
% 1.38/0.54    inference(resolution,[],[f54,f100])).
% 1.38/0.54  fof(f100,plain,(
% 1.38/0.54    ~v2_struct_0(sK1) | spl3_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f98])).
% 1.38/0.54  fof(f54,plain,(
% 1.38/0.54    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f21])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,axiom,(
% 1.38/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.38/0.54  fof(f196,plain,(
% 1.38/0.54    ~spl3_20 | ~spl3_11 | spl3_13),
% 1.38/0.54    inference(avatar_split_clause,[],[f191,f154,f140,f193])).
% 1.38/0.54  fof(f140,plain,(
% 1.38/0.54    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.38/0.54  fof(f154,plain,(
% 1.38/0.54    spl3_13 <=> r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.38/0.54  fof(f191,plain,(
% 1.38/0.54    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_11 | spl3_13)),
% 1.38/0.54    inference(forward_demodulation,[],[f156,f142])).
% 1.38/0.54  fof(f142,plain,(
% 1.38/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 1.38/0.54    inference(avatar_component_clause,[],[f140])).
% 1.38/0.54  fof(f156,plain,(
% 1.38/0.54    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_13),
% 1.38/0.54    inference(avatar_component_clause,[],[f154])).
% 1.38/0.54  fof(f190,plain,(
% 1.38/0.54    spl3_19 | ~spl3_11 | ~spl3_14),
% 1.38/0.54    inference(avatar_split_clause,[],[f185,f159,f140,f187])).
% 1.38/0.54  fof(f159,plain,(
% 1.38/0.54    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.38/0.54  fof(f185,plain,(
% 1.38/0.54    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_11 | ~spl3_14)),
% 1.38/0.54    inference(forward_demodulation,[],[f161,f142])).
% 1.38/0.54  fof(f161,plain,(
% 1.38/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_14),
% 1.38/0.54    inference(avatar_component_clause,[],[f159])).
% 1.38/0.54  fof(f184,plain,(
% 1.38/0.54    spl3_18 | ~spl3_11 | ~spl3_15),
% 1.38/0.54    inference(avatar_split_clause,[],[f179,f164,f140,f181])).
% 1.38/0.54  fof(f164,plain,(
% 1.38/0.54    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.38/0.54  fof(f179,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_11 | ~spl3_15)),
% 1.38/0.54    inference(forward_demodulation,[],[f166,f142])).
% 1.38/0.54  fof(f166,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 1.38/0.54    inference(avatar_component_clause,[],[f164])).
% 1.38/0.54  fof(f178,plain,(
% 1.38/0.54    spl3_17 | ~spl3_11 | ~spl3_16),
% 1.38/0.54    inference(avatar_split_clause,[],[f173,f169,f140,f175])).
% 1.38/0.54  fof(f169,plain,(
% 1.38/0.54    spl3_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.38/0.54  fof(f173,plain,(
% 1.38/0.54    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_11 | ~spl3_16)),
% 1.38/0.54    inference(forward_demodulation,[],[f171,f142])).
% 1.38/0.54  fof(f171,plain,(
% 1.38/0.54    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 1.38/0.54    inference(avatar_component_clause,[],[f169])).
% 1.38/0.54  fof(f172,plain,(
% 1.38/0.54    spl3_16 | ~spl3_8 | ~spl3_12),
% 1.38/0.54    inference(avatar_split_clause,[],[f152,f145,f123,f169])).
% 1.38/0.54  fof(f123,plain,(
% 1.38/0.54    spl3_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.38/0.54  fof(f145,plain,(
% 1.38/0.54    spl3_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.38/0.54  fof(f152,plain,(
% 1.38/0.54    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_8 | ~spl3_12)),
% 1.38/0.54    inference(backward_demodulation,[],[f125,f147])).
% 1.38/0.54  fof(f147,plain,(
% 1.38/0.54    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_12),
% 1.38/0.54    inference(avatar_component_clause,[],[f145])).
% 1.38/0.54  fof(f125,plain,(
% 1.38/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_8),
% 1.38/0.54    inference(avatar_component_clause,[],[f123])).
% 1.38/0.54  fof(f167,plain,(
% 1.38/0.54    spl3_15 | ~spl3_7 | ~spl3_12),
% 1.38/0.54    inference(avatar_split_clause,[],[f151,f145,f118,f164])).
% 1.38/0.54  fof(f118,plain,(
% 1.38/0.54    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.38/0.54  fof(f151,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_12)),
% 1.38/0.54    inference(backward_demodulation,[],[f120,f147])).
% 1.38/0.54  fof(f120,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 1.38/0.54    inference(avatar_component_clause,[],[f118])).
% 1.38/0.54  fof(f162,plain,(
% 1.38/0.54    spl3_14 | ~spl3_6 | ~spl3_12),
% 1.38/0.54    inference(avatar_split_clause,[],[f150,f145,f113,f159])).
% 1.38/0.54  fof(f113,plain,(
% 1.38/0.54    spl3_6 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.38/0.54  fof(f150,plain,(
% 1.38/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | ~spl3_12)),
% 1.38/0.54    inference(backward_demodulation,[],[f115,f147])).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~spl3_6),
% 1.38/0.54    inference(avatar_component_clause,[],[f113])).
% 1.38/0.54  fof(f157,plain,(
% 1.38/0.54    ~spl3_13 | spl3_4 | ~spl3_12),
% 1.38/0.54    inference(avatar_split_clause,[],[f149,f145,f103,f154])).
% 1.38/0.54  fof(f103,plain,(
% 1.38/0.54    spl3_4 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.38/0.54  fof(f149,plain,(
% 1.38/0.54    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_4 | ~spl3_12)),
% 1.38/0.54    inference(backward_demodulation,[],[f105,f147])).
% 1.38/0.54  fof(f105,plain,(
% 1.38/0.54    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_4),
% 1.38/0.54    inference(avatar_component_clause,[],[f103])).
% 1.38/0.54  fof(f148,plain,(
% 1.38/0.54    spl3_12 | ~spl3_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f138,f93,f145])).
% 1.38/0.54  fof(f138,plain,(
% 1.38/0.54    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_2),
% 1.38/0.54    inference(resolution,[],[f53,f95])).
% 1.38/0.54  fof(f95,plain,(
% 1.38/0.54    l1_struct_0(sK1) | ~spl3_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f93])).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f13])).
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.38/0.54  fof(f143,plain,(
% 1.38/0.54    spl3_11 | ~spl3_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f137,f88,f140])).
% 1.38/0.54  fof(f88,plain,(
% 1.38/0.54    spl3_1 <=> l1_struct_0(sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.38/0.54  fof(f137,plain,(
% 1.38/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_1),
% 1.38/0.54    inference(resolution,[],[f53,f90])).
% 1.38/0.54  fof(f90,plain,(
% 1.38/0.54    l1_struct_0(sK0) | ~spl3_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f88])).
% 1.38/0.54  fof(f136,plain,(
% 1.38/0.54    spl3_10),
% 1.38/0.54    inference(avatar_split_clause,[],[f52,f133])).
% 1.38/0.54  fof(f133,plain,(
% 1.38/0.54    spl3_10 <=> v1_xboole_0(k1_xboole_0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    v1_xboole_0(k1_xboole_0)),
% 1.38/0.54    inference(cnf_transformation,[],[f1])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    v1_xboole_0(k1_xboole_0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.38/0.54  fof(f131,plain,(
% 1.38/0.54    spl3_9),
% 1.38/0.54    inference(avatar_split_clause,[],[f43,f128])).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    v1_funct_1(sK2)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.38/0.54    inference(flattening,[],[f18])).
% 1.38/0.54  fof(f18,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f17])).
% 1.38/0.54  fof(f17,negated_conjecture,(
% 1.38/0.54    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.38/0.54    inference(negated_conjecture,[],[f16])).
% 1.38/0.54  fof(f16,conjecture,(
% 1.38/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.38/0.54  fof(f126,plain,(
% 1.38/0.54    spl3_8),
% 1.38/0.54    inference(avatar_split_clause,[],[f44,f123])).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f121,plain,(
% 1.38/0.54    spl3_7),
% 1.38/0.54    inference(avatar_split_clause,[],[f45,f118])).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f116,plain,(
% 1.38/0.54    spl3_6),
% 1.38/0.54    inference(avatar_split_clause,[],[f46,f113])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f111,plain,(
% 1.38/0.54    spl3_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f47,f108])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    v2_funct_1(sK2)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f106,plain,(
% 1.38/0.54    ~spl3_4),
% 1.38/0.54    inference(avatar_split_clause,[],[f48,f103])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f101,plain,(
% 1.38/0.54    ~spl3_3),
% 1.38/0.54    inference(avatar_split_clause,[],[f49,f98])).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    ~v2_struct_0(sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f96,plain,(
% 1.38/0.54    spl3_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f50,f93])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    l1_struct_0(sK1)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f91,plain,(
% 1.38/0.54    spl3_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f51,f88])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    l1_struct_0(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (22350)------------------------------
% 1.38/0.54  % (22350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22350)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (22350)Memory used [KB]: 6652
% 1.38/0.54  % (22350)Time elapsed: 0.071 s
% 1.38/0.54  % (22350)------------------------------
% 1.38/0.54  % (22350)------------------------------
% 1.38/0.54  % (22334)Success in time 0.18 s
%------------------------------------------------------------------------------
