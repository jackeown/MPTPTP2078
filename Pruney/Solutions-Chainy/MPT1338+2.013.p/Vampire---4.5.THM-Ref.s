%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 471 expanded)
%              Number of leaves         :   57 ( 208 expanded)
%              Depth                    :   13
%              Number of atoms          :  807 (1565 expanded)
%              Number of equality atoms :  174 ( 381 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f742,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f115,f120,f125,f130,f135,f155,f162,f183,f197,f202,f214,f222,f229,f246,f248,f249,f267,f291,f353,f385,f395,f401,f426,f431,f438,f449,f473,f482,f489,f490,f492,f686,f724,f740,f741])).

fof(f741,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f740,plain,
    ( ~ spl3_74
    | spl3_70
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f733,f721,f683,f737])).

fof(f737,plain,
    ( spl3_74
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f683,plain,
    ( spl3_70
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f721,plain,
    ( spl3_73
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f733,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl3_70
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f725,f685])).

fof(f685,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | spl3_70 ),
    inference(avatar_component_clause,[],[f683])).

fof(f725,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_73 ),
    inference(resolution,[],[f723,f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

% (15844)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f723,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f721])).

fof(f724,plain,
    ( spl3_73
    | ~ spl3_31
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f719,f470,f435,f293,f721])).

fof(f293,plain,
    ( spl3_31
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f435,plain,
    ( spl3_49
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f470,plain,
    ( spl3_53
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f719,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_31
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f541,f472])).

fof(f472,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f470])).

fof(f541,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_31
    | ~ spl3_49 ),
    inference(superposition,[],[f437,f295])).

fof(f295,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f293])).

fof(f437,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f435])).

fof(f686,plain,
    ( ~ spl3_70
    | ~ spl3_31
    | spl3_48
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f681,f470,f428,f293,f683])).

fof(f428,plain,
    ( spl3_48
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f681,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_31
    | spl3_48
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f680,f295])).

fof(f680,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2))
    | spl3_48
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f430,f472])).

fof(f430,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f428])).

fof(f492,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f490,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f489,plain,
    ( ~ spl3_1
    | spl3_28
    | ~ spl3_30
    | ~ spl3_38
    | spl3_40 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | ~ spl3_1
    | spl3_28
    | ~ spl3_30
    | ~ spl3_38
    | spl3_40 ),
    inference(subsumption_resolution,[],[f487,f352])).

fof(f352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl3_38
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f487,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_1
    | spl3_28
    | ~ spl3_30
    | spl3_40 ),
    inference(subsumption_resolution,[],[f486,f266])).

fof(f266,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_28
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f486,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_30
    | spl3_40 ),
    inference(resolution,[],[f396,f290])).

fof(f290,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) )
    | ~ spl3_1
    | spl3_40 ),
    inference(resolution,[],[f380,f102])).

fof(f102,plain,
    ( ! [X6,X7] :
        ( v1_partfun1(sK2,X6)
        | v1_xboole_0(X7)
        | ~ v1_funct_2(sK2,X6,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f77,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f380,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl3_40
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f482,plain,
    ( spl3_54
    | ~ spl3_22
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f447,f435,f219,f479])).

fof(f479,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f219,plain,
    ( spl3_22
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f447,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f443,f221])).

fof(f221,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f219])).

fof(f443,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(resolution,[],[f437,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f473,plain,
    ( spl3_53
    | ~ spl3_47
    | spl3_48
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f446,f435,f428,f423,f470])).

fof(f423,plain,
    ( spl3_47
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f446,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_47
    | spl3_48
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f445,f425])).

fof(f425,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f423])).

fof(f445,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | spl3_48
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f440,f430])).

fof(f440,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_49 ),
    inference(resolution,[],[f437,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f449,plain,
    ( spl3_42
    | ~ spl3_49 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl3_42
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f444,f390])).

fof(f390,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl3_42
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f444,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(resolution,[],[f437,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f438,plain,
    ( spl3_49
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f433,f398,f288,f235,f159,f75,f435])).

fof(f159,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f235,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f398,plain,
    ( spl3_44
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f433,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f432,f400])).

fof(f400,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f398])).

fof(f432,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f280,f290])).

fof(f280,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f279,f237])).

fof(f237,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f235])).

fof(f279,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f278,f237])).

fof(f278,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f101,f161])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f101,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_2(sK2,X4,X5)
        | m1_subset_1(k2_tops_2(X4,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f431,plain,
    ( ~ spl3_48
    | spl3_17
    | ~ spl3_25
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f421,f398,f235,f190,f428])).

fof(f190,plain,
    ( spl3_17
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f421,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_17
    | ~ spl3_25
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f259,f400])).

fof(f259,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_17
    | ~ spl3_25 ),
    inference(superposition,[],[f192,f237])).

fof(f192,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f190])).

fof(f426,plain,
    ( spl3_47
    | ~ spl3_1
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f405,f398,f350,f288,f75,f423])).

fof(f405,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f404,f290])).

fof(f404,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_38
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f403,f352])).

fof(f403,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_44 ),
    inference(superposition,[],[f100,f400])).

fof(f100,plain,
    ( ! [X2,X3] :
        ( v1_funct_2(k2_tops_2(X2,X3,sK2),X3,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(sK2,X2,X3) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f401,plain,
    ( spl3_44
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f348,f288,f239,f235,f159,f80,f75,f398])).

fof(f80,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f239,plain,
    ( spl3_26
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f348,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f347,f237])).

fof(f347,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f346,f241])).

fof(f241,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f239])).

fof(f346,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f345,f237])).

fof(f345,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f344,f290])).

fof(f344,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f343,f237])).

fof(f343,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f106,f161])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f103,f77])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_1(sK2)
        | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f82,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f395,plain,
    ( ~ spl3_42
    | ~ spl3_43
    | ~ spl3_21
    | ~ spl3_22
    | spl3_31 ),
    inference(avatar_split_clause,[],[f386,f293,f219,f211,f392,f388])).

fof(f392,plain,
    ( spl3_43
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f211,plain,
    ( spl3_21
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f386,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_22
    | spl3_31 ),
    inference(subsumption_resolution,[],[f224,f294])).

fof(f294,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f293])).

fof(f224,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f223,f213])).

fof(f213,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f211])).

fof(f223,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(superposition,[],[f45,f221])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f385,plain,
    ( ~ spl3_40
    | spl3_41
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f372,f199,f180,f382,f378])).

fof(f382,plain,
    ( spl3_41
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f180,plain,
    ( spl3_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f199,plain,
    ( spl3_19
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f372,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f188,f201])).

fof(f201,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl3_16 ),
    inference(resolution,[],[f182,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f182,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f353,plain,
    ( spl3_38
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f260,f235,f159,f350])).

fof(f260,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(superposition,[],[f161,f237])).

fof(f291,plain,
    ( spl3_30
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f277,f243,f235,f288])).

fof(f243,plain,
    ( spl3_27
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f277,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f245,f237])).

fof(f245,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f243])).

fof(f267,plain,
    ( ~ spl3_28
    | spl3_12
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f261,f235,f152,f264])).

fof(f152,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f261,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_12
    | ~ spl3_25 ),
    inference(superposition,[],[f154,f237])).

fof(f154,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f249,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f248,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f246,plain,
    ( spl3_27
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f148,f127,f117,f112,f243])).

fof(f112,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( spl3_7
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f127,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f148,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f146,f119])).

fof(f119,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f146,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f114,f129])).

fof(f129,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f114,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f229,plain,
    ( spl3_23
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f176,f159,f226])).

fof(f226,plain,
    ( spl3_23
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f176,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f161,f55])).

fof(f222,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f217,f180,f80,f75,f219])).

fof(f217,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f108,f182])).

fof(f108,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f105,f77])).

fof(f105,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f214,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f208,f180,f80,f75,f211])).

fof(f208,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f107,f182])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f104,f77])).

fof(f104,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f202,plain,
    ( spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f174,f159,f199])).

fof(f174,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f161,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f197,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f187,f127,f117,f194,f190])).

fof(f194,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f187,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f186,f129])).

fof(f186,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f185,f119])).

fof(f185,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f184,f129])).

fof(f184,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f36,f119])).

fof(f36,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f183,plain,
    ( spl3_16
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f177,f159,f180])).

fof(f177,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f161,f54])).

fof(f162,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f150,f127,f122,f117,f159])).

fof(f122,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f144,f129])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f124,f119])).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f155,plain,
    ( ~ spl3_12
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f143,f117,f90,f85,f152])).

fof(f85,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f143,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f142,f87])).

fof(f87,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f142,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f141,f92])).

fof(f92,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f141,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f48,f119])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f135,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f40,f132])).

fof(f132,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f40,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f130,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f110,f95,f127])).

fof(f95,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f110,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f97,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f125,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f39,f122])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f120,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f109,f90,f117])).

fof(f109,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f92,f47])).

fof(f115,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f38,f112])).

fof(f38,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f44,f95])).

fof(f44,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:46:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (15853)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.48  % (15843)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.49  % (15859)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.23/0.50  % (15851)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.50  % (15853)Refutation not found, incomplete strategy% (15853)------------------------------
% 0.23/0.50  % (15853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (15853)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (15853)Memory used [KB]: 1663
% 0.23/0.50  % (15853)Time elapsed: 0.074 s
% 0.23/0.50  % (15853)------------------------------
% 0.23/0.50  % (15853)------------------------------
% 0.23/0.51  % (15843)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f742,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f115,f120,f125,f130,f135,f155,f162,f183,f197,f202,f214,f222,f229,f246,f248,f249,f267,f291,f353,f385,f395,f401,f426,f431,f438,f449,f473,f482,f489,f490,f492,f686,f724,f740,f741])).
% 0.23/0.51  fof(f741,plain,(
% 0.23/0.51    k1_xboole_0 != k2_relat_1(sK2) | k2_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f740,plain,(
% 0.23/0.51    ~spl3_74 | spl3_70 | ~spl3_73),
% 0.23/0.51    inference(avatar_split_clause,[],[f733,f721,f683,f737])).
% 0.23/0.51  fof(f737,plain,(
% 0.23/0.51    spl3_74 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.23/0.51  fof(f683,plain,(
% 0.23/0.51    spl3_70 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.23/0.51  fof(f721,plain,(
% 0.23/0.51    spl3_73 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.23/0.51  fof(f733,plain,(
% 0.23/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl3_70 | ~spl3_73)),
% 0.23/0.51    inference(subsumption_resolution,[],[f725,f685])).
% 0.23/0.51  fof(f685,plain,(
% 0.23/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | spl3_70),
% 0.23/0.51    inference(avatar_component_clause,[],[f683])).
% 0.23/0.51  fof(f725,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~spl3_73),
% 0.23/0.51    inference(resolution,[],[f723,f69])).
% 0.23/0.51  fof(f69,plain,(
% 0.23/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.23/0.51    inference(equality_resolution,[],[f61])).
% 0.23/0.51  fof(f61,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  % (15844)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(flattening,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.23/0.51  fof(f723,plain,(
% 0.23/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_73),
% 0.23/0.51    inference(avatar_component_clause,[],[f721])).
% 0.23/0.51  fof(f724,plain,(
% 0.23/0.51    spl3_73 | ~spl3_31 | ~spl3_49 | ~spl3_53),
% 0.23/0.51    inference(avatar_split_clause,[],[f719,f470,f435,f293,f721])).
% 0.23/0.51  fof(f293,plain,(
% 0.23/0.51    spl3_31 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.23/0.51  fof(f435,plain,(
% 0.23/0.51    spl3_49 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.23/0.51  fof(f470,plain,(
% 0.23/0.51    spl3_53 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.23/0.51  fof(f719,plain,(
% 0.23/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_31 | ~spl3_49 | ~spl3_53)),
% 0.23/0.51    inference(forward_demodulation,[],[f541,f472])).
% 0.23/0.51  fof(f472,plain,(
% 0.23/0.51    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_53),
% 0.23/0.51    inference(avatar_component_clause,[],[f470])).
% 0.23/0.51  fof(f541,plain,(
% 0.23/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | (~spl3_31 | ~spl3_49)),
% 0.23/0.51    inference(superposition,[],[f437,f295])).
% 0.23/0.51  fof(f295,plain,(
% 0.23/0.51    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_31),
% 0.23/0.51    inference(avatar_component_clause,[],[f293])).
% 0.23/0.51  fof(f437,plain,(
% 0.23/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_49),
% 0.23/0.51    inference(avatar_component_clause,[],[f435])).
% 0.23/0.51  fof(f686,plain,(
% 0.23/0.51    ~spl3_70 | ~spl3_31 | spl3_48 | ~spl3_53),
% 0.23/0.51    inference(avatar_split_clause,[],[f681,f470,f428,f293,f683])).
% 0.23/0.51  fof(f428,plain,(
% 0.23/0.51    spl3_48 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.23/0.51  fof(f681,plain,(
% 0.23/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | (~spl3_31 | spl3_48 | ~spl3_53)),
% 0.23/0.51    inference(forward_demodulation,[],[f680,f295])).
% 0.23/0.51  fof(f680,plain,(
% 0.23/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) | (spl3_48 | ~spl3_53)),
% 0.23/0.51    inference(forward_demodulation,[],[f430,f472])).
% 0.23/0.51  fof(f430,plain,(
% 0.23/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | spl3_48),
% 0.23/0.51    inference(avatar_component_clause,[],[f428])).
% 0.23/0.51  fof(f492,plain,(
% 0.23/0.51    k1_xboole_0 != k2_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f490,plain,(
% 0.23/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f489,plain,(
% 0.23/0.51    ~spl3_1 | spl3_28 | ~spl3_30 | ~spl3_38 | spl3_40),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f488])).
% 0.23/0.51  fof(f488,plain,(
% 0.23/0.51    $false | (~spl3_1 | spl3_28 | ~spl3_30 | ~spl3_38 | spl3_40)),
% 0.23/0.51    inference(subsumption_resolution,[],[f487,f352])).
% 0.23/0.51  fof(f352,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_38),
% 0.23/0.51    inference(avatar_component_clause,[],[f350])).
% 0.23/0.51  fof(f350,plain,(
% 0.23/0.51    spl3_38 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.23/0.51  fof(f487,plain,(
% 0.23/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_1 | spl3_28 | ~spl3_30 | spl3_40)),
% 0.23/0.51    inference(subsumption_resolution,[],[f486,f266])).
% 0.23/0.51  fof(f266,plain,(
% 0.23/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_28),
% 0.23/0.51    inference(avatar_component_clause,[],[f264])).
% 0.23/0.51  fof(f264,plain,(
% 0.23/0.51    spl3_28 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.23/0.51  fof(f486,plain,(
% 0.23/0.51    v1_xboole_0(k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_30 | spl3_40)),
% 0.23/0.51    inference(resolution,[],[f396,f290])).
% 0.23/0.51  fof(f290,plain,(
% 0.23/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_30),
% 0.23/0.51    inference(avatar_component_clause,[],[f288])).
% 0.23/0.51  fof(f288,plain,(
% 0.23/0.51    spl3_30 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.23/0.51  fof(f396,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | (~spl3_1 | spl3_40)),
% 0.23/0.51    inference(resolution,[],[f380,f102])).
% 0.23/0.51  fof(f102,plain,(
% 0.23/0.51    ( ! [X6,X7] : (v1_partfun1(sK2,X6) | v1_xboole_0(X7) | ~v1_funct_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f77,f51])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.23/0.51    inference(flattening,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    v1_funct_1(sK2) | ~spl3_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f75])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    spl3_1 <=> v1_funct_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.51  fof(f380,plain,(
% 0.23/0.51    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_40),
% 0.23/0.51    inference(avatar_component_clause,[],[f378])).
% 0.23/0.51  fof(f378,plain,(
% 0.23/0.51    spl3_40 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.23/0.51  fof(f482,plain,(
% 0.23/0.51    spl3_54 | ~spl3_22 | ~spl3_49),
% 0.23/0.51    inference(avatar_split_clause,[],[f447,f435,f219,f479])).
% 0.23/0.51  fof(f479,plain,(
% 0.23/0.51    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.23/0.51  fof(f219,plain,(
% 0.23/0.51    spl3_22 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.23/0.51  fof(f447,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_22 | ~spl3_49)),
% 0.23/0.51    inference(forward_demodulation,[],[f443,f221])).
% 0.23/0.51  fof(f221,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.23/0.51    inference(avatar_component_clause,[],[f219])).
% 0.23/0.51  fof(f443,plain,(
% 0.23/0.51    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_49),
% 0.23/0.51    inference(resolution,[],[f437,f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.51  fof(f473,plain,(
% 0.23/0.51    spl3_53 | ~spl3_47 | spl3_48 | ~spl3_49),
% 0.23/0.51    inference(avatar_split_clause,[],[f446,f435,f428,f423,f470])).
% 0.23/0.51  fof(f423,plain,(
% 0.23/0.51    spl3_47 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.23/0.51  fof(f446,plain,(
% 0.23/0.51    k1_xboole_0 = k2_struct_0(sK0) | (~spl3_47 | spl3_48 | ~spl3_49)),
% 0.23/0.51    inference(subsumption_resolution,[],[f445,f425])).
% 0.23/0.51  fof(f425,plain,(
% 0.23/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_47),
% 0.23/0.51    inference(avatar_component_clause,[],[f423])).
% 0.23/0.51  fof(f445,plain,(
% 0.23/0.51    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (spl3_48 | ~spl3_49)),
% 0.23/0.51    inference(subsumption_resolution,[],[f440,f430])).
% 0.23/0.51  fof(f440,plain,(
% 0.23/0.51    k1_xboole_0 = k2_struct_0(sK0) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_49),
% 0.23/0.51    inference(resolution,[],[f437,f63])).
% 0.23/0.51  fof(f63,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f449,plain,(
% 0.23/0.51    spl3_42 | ~spl3_49),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f448])).
% 0.23/0.51  fof(f448,plain,(
% 0.23/0.51    $false | (spl3_42 | ~spl3_49)),
% 0.23/0.51    inference(subsumption_resolution,[],[f444,f390])).
% 0.23/0.51  fof(f390,plain,(
% 0.23/0.51    ~v1_relat_1(k2_funct_1(sK2)) | spl3_42),
% 0.23/0.51    inference(avatar_component_clause,[],[f388])).
% 0.23/0.51  fof(f388,plain,(
% 0.23/0.51    spl3_42 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.23/0.51  fof(f444,plain,(
% 0.23/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl3_49),
% 0.23/0.51    inference(resolution,[],[f437,f54])).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.51  fof(f438,plain,(
% 0.23/0.51    spl3_49 | ~spl3_1 | ~spl3_13 | ~spl3_25 | ~spl3_30 | ~spl3_44),
% 0.23/0.51    inference(avatar_split_clause,[],[f433,f398,f288,f235,f159,f75,f435])).
% 0.23/0.51  fof(f159,plain,(
% 0.23/0.51    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.23/0.51  fof(f235,plain,(
% 0.23/0.51    spl3_25 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.23/0.51  fof(f398,plain,(
% 0.23/0.51    spl3_44 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.23/0.51  fof(f433,plain,(
% 0.23/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13 | ~spl3_25 | ~spl3_30 | ~spl3_44)),
% 0.23/0.51    inference(forward_demodulation,[],[f432,f400])).
% 0.23/0.51  fof(f400,plain,(
% 0.23/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_44),
% 0.23/0.51    inference(avatar_component_clause,[],[f398])).
% 0.23/0.51  fof(f432,plain,(
% 0.23/0.51    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13 | ~spl3_25 | ~spl3_30)),
% 0.23/0.51    inference(subsumption_resolution,[],[f280,f290])).
% 0.23/0.51  fof(f280,plain,(
% 0.23/0.51    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_13 | ~spl3_25)),
% 0.23/0.51    inference(forward_demodulation,[],[f279,f237])).
% 0.23/0.51  fof(f237,plain,(
% 0.23/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_25),
% 0.23/0.51    inference(avatar_component_clause,[],[f235])).
% 0.23/0.51  fof(f279,plain,(
% 0.23/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13 | ~spl3_25)),
% 0.23/0.51    inference(forward_demodulation,[],[f278,f237])).
% 0.23/0.51  fof(f278,plain,(
% 0.23/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13)),
% 0.23/0.51    inference(resolution,[],[f101,f161])).
% 0.23/0.51  fof(f161,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.23/0.51    inference(avatar_component_clause,[],[f159])).
% 0.23/0.51  fof(f101,plain,(
% 0.23/0.51    ( ! [X4,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK2,X4,X5) | m1_subset_1(k2_tops_2(X4,X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f77,f66])).
% 0.23/0.51  fof(f66,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.23/0.51    inference(flattening,[],[f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.23/0.51  fof(f431,plain,(
% 0.23/0.51    ~spl3_48 | spl3_17 | ~spl3_25 | ~spl3_44),
% 0.23/0.51    inference(avatar_split_clause,[],[f421,f398,f235,f190,f428])).
% 0.23/0.51  fof(f190,plain,(
% 0.23/0.51    spl3_17 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.51  fof(f421,plain,(
% 0.23/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_17 | ~spl3_25 | ~spl3_44)),
% 0.23/0.51    inference(forward_demodulation,[],[f259,f400])).
% 0.23/0.51  fof(f259,plain,(
% 0.23/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_17 | ~spl3_25)),
% 0.23/0.51    inference(superposition,[],[f192,f237])).
% 0.23/0.51  fof(f192,plain,(
% 0.23/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_17),
% 0.23/0.51    inference(avatar_component_clause,[],[f190])).
% 0.23/0.51  fof(f426,plain,(
% 0.23/0.51    spl3_47 | ~spl3_1 | ~spl3_30 | ~spl3_38 | ~spl3_44),
% 0.23/0.51    inference(avatar_split_clause,[],[f405,f398,f350,f288,f75,f423])).
% 0.23/0.51  fof(f405,plain,(
% 0.23/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_30 | ~spl3_38 | ~spl3_44)),
% 0.23/0.51    inference(subsumption_resolution,[],[f404,f290])).
% 0.23/0.51  fof(f404,plain,(
% 0.23/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_38 | ~spl3_44)),
% 0.23/0.51    inference(subsumption_resolution,[],[f403,f352])).
% 0.23/0.51  fof(f403,plain,(
% 0.23/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_44)),
% 0.23/0.51    inference(superposition,[],[f100,f400])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    ( ! [X2,X3] : (v1_funct_2(k2_tops_2(X2,X3,sK2),X3,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3)) ) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f77,f65])).
% 0.23/0.51  fof(f65,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f33])).
% 0.23/0.51  fof(f401,plain,(
% 0.23/0.51    spl3_44 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_30),
% 0.23/0.51    inference(avatar_split_clause,[],[f348,f288,f239,f235,f159,f80,f75,f398])).
% 0.23/0.51  fof(f80,plain,(
% 0.23/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.51  fof(f239,plain,(
% 0.23/0.51    spl3_26 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.23/0.51  fof(f348,plain,(
% 0.23/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_30)),
% 0.23/0.51    inference(forward_demodulation,[],[f347,f237])).
% 0.23/0.51  fof(f347,plain,(
% 0.23/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_30)),
% 0.23/0.51    inference(subsumption_resolution,[],[f346,f241])).
% 0.23/0.51  fof(f241,plain,(
% 0.23/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_26),
% 0.23/0.51    inference(avatar_component_clause,[],[f239])).
% 0.23/0.51  fof(f346,plain,(
% 0.23/0.51    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_30)),
% 0.23/0.51    inference(forward_demodulation,[],[f345,f237])).
% 0.23/0.51  fof(f345,plain,(
% 0.23/0.51    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_30)),
% 0.23/0.51    inference(subsumption_resolution,[],[f344,f290])).
% 0.23/0.51  fof(f344,plain,(
% 0.23/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25)),
% 0.23/0.51    inference(forward_demodulation,[],[f343,f237])).
% 0.23/0.51  fof(f343,plain,(
% 0.23/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.23/0.51    inference(resolution,[],[f106,f161])).
% 0.23/0.51  fof(f106,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.23/0.51    inference(subsumption_resolution,[],[f103,f77])).
% 0.23/0.51  fof(f103,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)) ) | ~spl3_2),
% 0.23/0.51    inference(resolution,[],[f82,f67])).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.23/0.51    inference(flattening,[],[f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.23/0.51  fof(f82,plain,(
% 0.23/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f80])).
% 0.23/0.51  fof(f395,plain,(
% 0.23/0.51    ~spl3_42 | ~spl3_43 | ~spl3_21 | ~spl3_22 | spl3_31),
% 0.23/0.51    inference(avatar_split_clause,[],[f386,f293,f219,f211,f392,f388])).
% 0.23/0.51  fof(f392,plain,(
% 0.23/0.51    spl3_43 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.23/0.51  fof(f211,plain,(
% 0.23/0.51    spl3_21 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.23/0.51  fof(f386,plain,(
% 0.23/0.51    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_21 | ~spl3_22 | spl3_31)),
% 0.23/0.51    inference(subsumption_resolution,[],[f224,f294])).
% 0.23/0.51  fof(f294,plain,(
% 0.23/0.51    k1_xboole_0 != k2_relat_1(sK2) | spl3_31),
% 0.23/0.51    inference(avatar_component_clause,[],[f293])).
% 0.23/0.51  fof(f224,plain,(
% 0.23/0.51    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_21 | ~spl3_22)),
% 0.23/0.51    inference(forward_demodulation,[],[f223,f213])).
% 0.23/0.51  fof(f213,plain,(
% 0.23/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_21),
% 0.23/0.51    inference(avatar_component_clause,[],[f211])).
% 0.23/0.51  fof(f223,plain,(
% 0.23/0.51    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.23/0.51    inference(superposition,[],[f45,f221])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) )),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.23/0.51  fof(f385,plain,(
% 0.23/0.51    ~spl3_40 | spl3_41 | ~spl3_16 | ~spl3_19),
% 0.23/0.51    inference(avatar_split_clause,[],[f372,f199,f180,f382,f378])).
% 0.23/0.51  fof(f382,plain,(
% 0.23/0.51    spl3_41 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.23/0.51  fof(f180,plain,(
% 0.23/0.51    spl3_16 <=> v1_relat_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.23/0.51  fof(f199,plain,(
% 0.23/0.51    spl3_19 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.23/0.51  fof(f372,plain,(
% 0.23/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_16 | ~spl3_19)),
% 0.23/0.51    inference(resolution,[],[f188,f201])).
% 0.23/0.51  fof(f201,plain,(
% 0.23/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_19),
% 0.23/0.51    inference(avatar_component_clause,[],[f199])).
% 0.23/0.51  fof(f188,plain,(
% 0.23/0.51    ( ! [X0] : (~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v1_partfun1(sK2,X0)) ) | ~spl3_16),
% 0.23/0.51    inference(resolution,[],[f182,f53])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(flattening,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.23/0.51  fof(f182,plain,(
% 0.23/0.51    v1_relat_1(sK2) | ~spl3_16),
% 0.23/0.51    inference(avatar_component_clause,[],[f180])).
% 0.23/0.51  fof(f353,plain,(
% 0.23/0.51    spl3_38 | ~spl3_13 | ~spl3_25),
% 0.23/0.51    inference(avatar_split_clause,[],[f260,f235,f159,f350])).
% 0.23/0.51  fof(f260,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_25)),
% 0.23/0.51    inference(superposition,[],[f161,f237])).
% 0.23/0.51  fof(f291,plain,(
% 0.23/0.51    spl3_30 | ~spl3_25 | ~spl3_27),
% 0.23/0.51    inference(avatar_split_clause,[],[f277,f243,f235,f288])).
% 0.23/0.51  fof(f243,plain,(
% 0.23/0.51    spl3_27 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.23/0.51  fof(f277,plain,(
% 0.23/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_25 | ~spl3_27)),
% 0.23/0.51    inference(forward_demodulation,[],[f245,f237])).
% 0.23/0.51  fof(f245,plain,(
% 0.23/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_27),
% 0.23/0.51    inference(avatar_component_clause,[],[f243])).
% 0.23/0.51  fof(f267,plain,(
% 0.23/0.51    ~spl3_28 | spl3_12 | ~spl3_25),
% 0.23/0.51    inference(avatar_split_clause,[],[f261,f235,f152,f264])).
% 0.23/0.51  fof(f152,plain,(
% 0.23/0.51    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.23/0.51  fof(f261,plain,(
% 0.23/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_12 | ~spl3_25)),
% 0.23/0.51    inference(superposition,[],[f154,f237])).
% 0.23/0.51  fof(f154,plain,(
% 0.23/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_12),
% 0.23/0.51    inference(avatar_component_clause,[],[f152])).
% 0.23/0.51  fof(f249,plain,(
% 0.23/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f248,plain,(
% 0.23/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f246,plain,(
% 0.23/0.51    spl3_27 | ~spl3_6 | ~spl3_7 | ~spl3_9),
% 0.23/0.51    inference(avatar_split_clause,[],[f148,f127,f117,f112,f243])).
% 0.23/0.51  fof(f112,plain,(
% 0.23/0.51    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.51  fof(f117,plain,(
% 0.23/0.51    spl3_7 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.51  fof(f127,plain,(
% 0.23/0.51    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.51  fof(f148,plain,(
% 0.23/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_9)),
% 0.23/0.51    inference(forward_demodulation,[],[f146,f119])).
% 0.23/0.51  fof(f119,plain,(
% 0.23/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_7),
% 0.23/0.51    inference(avatar_component_clause,[],[f117])).
% 0.23/0.51  fof(f146,plain,(
% 0.23/0.51    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_6 | ~spl3_9)),
% 0.23/0.51    inference(superposition,[],[f114,f129])).
% 0.23/0.51  fof(f129,plain,(
% 0.23/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.23/0.51    inference(avatar_component_clause,[],[f127])).
% 0.23/0.51  fof(f114,plain,(
% 0.23/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.23/0.51    inference(avatar_component_clause,[],[f112])).
% 0.23/0.51  fof(f229,plain,(
% 0.23/0.51    spl3_23 | ~spl3_13),
% 0.23/0.51    inference(avatar_split_clause,[],[f176,f159,f226])).
% 0.23/0.51  fof(f226,plain,(
% 0.23/0.51    spl3_23 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.23/0.51  fof(f176,plain,(
% 0.23/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.23/0.51    inference(resolution,[],[f161,f55])).
% 0.23/0.51  fof(f222,plain,(
% 0.23/0.51    spl3_22 | ~spl3_1 | ~spl3_2 | ~spl3_16),
% 0.23/0.51    inference(avatar_split_clause,[],[f217,f180,f80,f75,f219])).
% 0.23/0.51  fof(f217,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_16)),
% 0.23/0.51    inference(subsumption_resolution,[],[f108,f182])).
% 0.23/0.51  fof(f108,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.23/0.51    inference(subsumption_resolution,[],[f105,f77])).
% 0.23/0.51  fof(f105,plain,(
% 0.23/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.23/0.51    inference(resolution,[],[f82,f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(flattening,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.23/0.51  fof(f214,plain,(
% 0.23/0.51    spl3_21 | ~spl3_1 | ~spl3_2 | ~spl3_16),
% 0.23/0.51    inference(avatar_split_clause,[],[f208,f180,f80,f75,f211])).
% 0.23/0.51  fof(f208,plain,(
% 0.23/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_16)),
% 0.23/0.51    inference(subsumption_resolution,[],[f107,f182])).
% 0.23/0.51  fof(f107,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.23/0.51    inference(subsumption_resolution,[],[f104,f77])).
% 0.23/0.51  fof(f104,plain,(
% 0.23/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.23/0.51    inference(resolution,[],[f82,f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f202,plain,(
% 0.23/0.51    spl3_19 | ~spl3_13),
% 0.23/0.51    inference(avatar_split_clause,[],[f174,f159,f199])).
% 0.23/0.51  fof(f174,plain,(
% 0.23/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.23/0.51    inference(resolution,[],[f161,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.51  fof(f197,plain,(
% 0.23/0.51    ~spl3_17 | ~spl3_18 | ~spl3_7 | ~spl3_9),
% 0.23/0.51    inference(avatar_split_clause,[],[f187,f127,f117,f194,f190])).
% 0.23/0.51  fof(f194,plain,(
% 0.23/0.51    spl3_18 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.23/0.51  fof(f187,plain,(
% 0.23/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.23/0.51    inference(forward_demodulation,[],[f186,f129])).
% 0.23/0.51  fof(f186,plain,(
% 0.23/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.23/0.51    inference(forward_demodulation,[],[f185,f119])).
% 0.23/0.51  fof(f185,plain,(
% 0.23/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.23/0.51    inference(forward_demodulation,[],[f184,f129])).
% 0.23/0.51  fof(f184,plain,(
% 0.23/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl3_7),
% 0.23/0.51    inference(forward_demodulation,[],[f36,f119])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,negated_conjecture,(
% 0.23/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.23/0.51    inference(negated_conjecture,[],[f13])).
% 0.23/0.51  fof(f13,conjecture,(
% 0.23/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.23/0.51  fof(f183,plain,(
% 0.23/0.51    spl3_16 | ~spl3_13),
% 0.23/0.51    inference(avatar_split_clause,[],[f177,f159,f180])).
% 0.23/0.51  fof(f177,plain,(
% 0.23/0.51    v1_relat_1(sK2) | ~spl3_13),
% 0.23/0.51    inference(resolution,[],[f161,f54])).
% 0.23/0.51  fof(f162,plain,(
% 0.23/0.51    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.23/0.51    inference(avatar_split_clause,[],[f150,f127,f122,f117,f159])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.51  fof(f150,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.23/0.51    inference(forward_demodulation,[],[f144,f129])).
% 0.23/0.51  fof(f144,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.23/0.51    inference(forward_demodulation,[],[f124,f119])).
% 0.23/0.51  fof(f124,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.23/0.51    inference(avatar_component_clause,[],[f122])).
% 0.23/0.51  fof(f155,plain,(
% 0.23/0.51    ~spl3_12 | spl3_3 | ~spl3_4 | ~spl3_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f143,f117,f90,f85,f152])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    spl3_3 <=> v2_struct_0(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    spl3_4 <=> l1_struct_0(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.51  fof(f143,plain,(
% 0.23/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.23/0.51    inference(subsumption_resolution,[],[f142,f87])).
% 0.23/0.51  fof(f87,plain,(
% 0.23/0.51    ~v2_struct_0(sK1) | spl3_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f85])).
% 0.23/0.51  fof(f142,plain,(
% 0.23/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_7)),
% 0.23/0.51    inference(subsumption_resolution,[],[f141,f92])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    l1_struct_0(sK1) | ~spl3_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f90])).
% 0.23/0.51  fof(f141,plain,(
% 0.23/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_7),
% 0.23/0.51    inference(superposition,[],[f48,f119])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.23/0.51    inference(flattening,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.23/0.51  fof(f135,plain,(
% 0.23/0.51    spl3_10),
% 0.23/0.51    inference(avatar_split_clause,[],[f40,f132])).
% 0.23/0.51  fof(f132,plain,(
% 0.23/0.51    spl3_10 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f130,plain,(
% 0.23/0.51    spl3_9 | ~spl3_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f110,f95,f127])).
% 0.23/0.51  fof(f95,plain,(
% 0.23/0.51    spl3_5 <=> l1_struct_0(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.51  fof(f110,plain,(
% 0.23/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.23/0.51    inference(resolution,[],[f97,f47])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.51  fof(f97,plain,(
% 0.23/0.51    l1_struct_0(sK0) | ~spl3_5),
% 0.23/0.51    inference(avatar_component_clause,[],[f95])).
% 0.23/0.51  fof(f125,plain,(
% 0.23/0.51    spl3_8),
% 0.23/0.51    inference(avatar_split_clause,[],[f39,f122])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f120,plain,(
% 0.23/0.51    spl3_7 | ~spl3_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f109,f90,f117])).
% 0.23/0.51  fof(f109,plain,(
% 0.23/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.23/0.51    inference(resolution,[],[f92,f47])).
% 0.23/0.51  fof(f115,plain,(
% 0.23/0.51    spl3_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f38,f112])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f98,plain,(
% 0.23/0.51    spl3_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f44,f95])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    l1_struct_0(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f93,plain,(
% 0.23/0.51    spl3_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f43,f90])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    l1_struct_0(sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f88,plain,(
% 0.23/0.51    ~spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f42,f85])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ~v2_struct_0(sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f83,plain,(
% 0.23/0.51    spl3_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f41,f80])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    v2_funct_1(sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f37,f75])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    v1_funct_1(sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (15843)------------------------------
% 0.23/0.51  % (15843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (15843)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (15843)Memory used [KB]: 11001
% 0.23/0.51  % (15843)Time elapsed: 0.076 s
% 0.23/0.51  % (15843)------------------------------
% 0.23/0.51  % (15843)------------------------------
% 0.23/0.51  % (15839)Success in time 0.142 s
%------------------------------------------------------------------------------
