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
% DateTime   : Thu Dec  3 13:14:23 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  265 ( 489 expanded)
%              Number of leaves         :   73 ( 233 expanded)
%              Depth                    :    9
%              Number of atoms          :  931 (1674 expanded)
%              Number of equality atoms :  157 ( 266 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1841,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f139,f144,f149,f154,f159,f164,f169,f174,f188,f193,f199,f205,f215,f225,f238,f240,f245,f256,f301,f333,f426,f454,f477,f488,f515,f541,f594,f633,f676,f688,f690,f701,f733,f738,f743,f825,f878,f917,f1139,f1149,f1154,f1160,f1184,f1540,f1807,f1822,f1840])).

fof(f1840,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1822,plain,
    ( ~ spl5_28
    | ~ spl5_222
    | ~ spl5_20
    | ~ spl5_143
    | spl5_224
    | ~ spl5_144
    | ~ spl5_188 ),
    inference(avatar_split_clause,[],[f1817,f1537,f1151,f1819,f1146,f242,f1804,f298])).

fof(f298,plain,
    ( spl5_28
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1804,plain,
    ( spl5_222
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).

fof(f242,plain,
    ( spl5_20
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1146,plain,
    ( spl5_143
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f1819,plain,
    ( spl5_224
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f1151,plain,
    ( spl5_144
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f1537,plain,
    ( spl5_188
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f1817,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl5_144
    | ~ spl5_188 ),
    inference(forward_demodulation,[],[f1794,f1539])).

fof(f1539,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl5_188 ),
    inference(avatar_component_clause,[],[f1537])).

fof(f1794,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl5_144 ),
    inference(resolution,[],[f1153,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f1153,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl5_144 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1807,plain,
    ( spl5_222
    | ~ spl5_63
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f1802,f1151,f538,f1804])).

fof(f538,plain,
    ( spl5_63
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f1802,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl5_63
    | ~ spl5_144 ),
    inference(forward_demodulation,[],[f1788,f540])).

fof(f540,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f538])).

fof(f1788,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl5_144 ),
    inference(resolution,[],[f1153,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1540,plain,
    ( ~ spl5_15
    | ~ spl5_20
    | spl5_188
    | ~ spl5_28
    | ~ spl5_59
    | ~ spl5_63
    | ~ spl5_100
    | ~ spl5_109 ),
    inference(avatar_split_clause,[],[f1535,f894,f823,f538,f512,f298,f1537,f242,f208])).

fof(f208,plain,
    ( spl5_15
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f512,plain,
    ( spl5_59
  <=> k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f823,plain,
    ( spl5_100
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | k2_funct_1(X0) = sK2
        | k6_partfun1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
        | k1_relat_1(X0) != k2_relat_1(sK2)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f894,plain,
    ( spl5_109
  <=> k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f1535,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_28
    | ~ spl5_59
    | ~ spl5_63
    | ~ spl5_100
    | ~ spl5_109 ),
    inference(trivial_inequality_removal,[],[f1534])).

fof(f1534,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_28
    | ~ spl5_59
    | ~ spl5_63
    | ~ spl5_100
    | ~ spl5_109 ),
    inference(forward_demodulation,[],[f1533,f514])).

fof(f514,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f512])).

fof(f1533,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_28
    | ~ spl5_63
    | ~ spl5_100
    | ~ spl5_109 ),
    inference(trivial_inequality_removal,[],[f1532])).

fof(f1532,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_28
    | ~ spl5_63
    | ~ spl5_100
    | ~ spl5_109 ),
    inference(forward_demodulation,[],[f1531,f896])).

fof(f896,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f894])).

fof(f1531,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_28
    | ~ spl5_63
    | ~ spl5_100 ),
    inference(forward_demodulation,[],[f1513,f540])).

fof(f1513,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_28
    | ~ spl5_100 ),
    inference(resolution,[],[f824,f300])).

fof(f300,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f298])).

fof(f824,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k2_funct_1(X0) = sK2
        | k6_partfun1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
        | k1_relat_1(X0) != k2_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f823])).

fof(f1184,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1160,plain,
    ( spl5_109
    | spl5_43
    | ~ spl5_5
    | ~ spl5_141
    | ~ spl5_9
    | ~ spl5_45
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f1129,f485,f423,f171,f1136,f151,f395,f894])).

fof(f395,plain,
    ( spl5_43
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f151,plain,
    ( spl5_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1136,plain,
    ( spl5_141
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f171,plain,
    ( spl5_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f423,plain,
    ( spl5_45
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f485,plain,
    ( spl5_55
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f1129,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl5_55 ),
    inference(resolution,[],[f487,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f485])).

fof(f1154,plain,
    ( spl5_144
    | ~ spl5_141
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_45
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f1127,f485,f423,f171,f151,f1136,f1151])).

fof(f1127,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl5_55 ),
    inference(resolution,[],[f487,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f1149,plain,
    ( spl5_143
    | ~ spl5_141
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_45
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f1126,f485,f423,f171,f151,f1136,f1146])).

fof(f1126,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl5_55 ),
    inference(resolution,[],[f487,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1139,plain,
    ( spl5_141
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f1122,f485,f1136])).

fof(f1122,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl5_55 ),
    inference(resolution,[],[f487,f112])).

fof(f917,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f878,plain,
    ( spl5_107
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_87
    | ~ spl5_88
    | ~ spl5_89 ),
    inference(avatar_split_clause,[],[f873,f740,f735,f730,f171,f151,f875])).

fof(f875,plain,
    ( spl5_107
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f730,plain,
    ( spl5_87
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f735,plain,
    ( spl5_88
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f740,plain,
    ( spl5_89
  <=> k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f873,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl5_88
    | ~ spl5_89 ),
    inference(trivial_inequality_removal,[],[f872])).

fof(f872,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl5_88
    | ~ spl5_89 ),
    inference(forward_demodulation,[],[f868,f742])).

fof(f742,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f740])).

fof(f868,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl5_88 ),
    inference(resolution,[],[f118,f737])).

fof(f737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f735])).

fof(f825,plain,
    ( ~ spl5_16
    | spl5_100
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f818,f171,f823,f212])).

fof(f212,plain,
    ( spl5_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f818,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK2)
        | k6_partfun1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
        | k2_funct_1(X0) = sK2 )
    | ~ spl5_9 ),
    inference(resolution,[],[f124,f173])).

fof(f173,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f743,plain,
    ( spl5_89
    | ~ spl5_21
    | ~ spl5_83 ),
    inference(avatar_split_clause,[],[f717,f683,f253,f740])).

fof(f253,plain,
    ( spl5_21
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f683,plain,
    ( spl5_83
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f717,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl5_21
    | ~ spl5_83 ),
    inference(backward_demodulation,[],[f255,f685])).

fof(f685,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f683])).

fof(f255,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f253])).

fof(f738,plain,
    ( spl5_88
    | ~ spl5_17
    | ~ spl5_83 ),
    inference(avatar_split_clause,[],[f716,f683,f222,f735])).

fof(f222,plain,
    ( spl5_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f716,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl5_17
    | ~ spl5_83 ),
    inference(backward_demodulation,[],[f224,f685])).

fof(f224,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f222])).

fof(f733,plain,
    ( spl5_87
    | ~ spl5_14
    | ~ spl5_83 ),
    inference(avatar_split_clause,[],[f715,f683,f202,f730])).

fof(f202,plain,
    ( spl5_14
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f715,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl5_14
    | ~ spl5_83 ),
    inference(backward_demodulation,[],[f204,f685])).

fof(f204,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f202])).

fof(f701,plain,
    ( spl5_78
    | spl5_84
    | ~ spl5_9
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f693,f222,f202,f171,f698,f630])).

fof(f630,plain,
    ( spl5_78
  <=> sP4(k2_struct_0(sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f698,plain,
    ( spl5_84
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f693,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)
    | sP4(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl5_17 ),
    inference(resolution,[],[f128,f224])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | r2_funct_2(X0,X1,X2,X2)
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f128_D])).

fof(f128_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | r2_funct_2(X0,X1,X2,X2) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f690,plain,
    ( ~ spl5_16
    | spl5_83
    | ~ spl5_32
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f689,f669,f330,f683,f212])).

fof(f330,plain,
    ( spl5_32
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f669,plain,
    ( spl5_81
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f689,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_81 ),
    inference(resolution,[],[f671,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f671,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f669])).

fof(f688,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f687,f673,f136,f141])).

fof(f141,plain,
    ( spl5_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f136,plain,
    ( spl5_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f673,plain,
    ( spl5_82
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f687,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_82 ),
    inference(resolution,[],[f675,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f675,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f673])).

fof(f676,plain,
    ( spl5_81
    | ~ spl5_14
    | ~ spl5_9
    | spl5_82
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f664,f222,f673,f171,f202,f669])).

fof(f664,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl5_17 ),
    inference(resolution,[],[f96,f224])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f633,plain,
    ( ~ spl5_78
    | ~ spl5_9
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f609,f222,f202,f171,f630])).

fof(f609,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ sP4(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl5_17 ),
    inference(resolution,[],[f129,f224])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP4(X1,X0) ) ),
    inference(general_splitting,[],[f121,f128_D])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f594,plain,
    ( spl5_71
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f586,f222,f591])).

fof(f591,plain,
    ( spl5_71
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f586,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f112,f224])).

fof(f541,plain,
    ( spl5_63
    | ~ spl5_16
    | ~ spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f532,f151,f171,f212,f538])).

fof(f532,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f91,f153])).

fof(f153,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f515,plain,
    ( spl5_59
    | ~ spl5_16
    | ~ spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f506,f151,f171,f212,f512])).

fof(f506,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f90,f153])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f488,plain,
    ( spl5_55
    | ~ spl5_16
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f480,f171,f212,f485])).

fof(f480,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl5_9 ),
    inference(resolution,[],[f87,f173])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f477,plain,(
    ~ spl5_50 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl5_50 ),
    inference(resolution,[],[f453,f108])).

fof(f108,plain,(
    ! [X0,X1] : v1_xboole_0(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

fof(f453,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl5_50
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f454,plain,
    ( spl5_49
    | spl5_50 ),
    inference(avatar_split_clause,[],[f442,f452,f448])).

fof(f448,plain,
    ( spl5_49
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f442,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f97,f217])).

fof(f217,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f102,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f426,plain,
    ( spl5_45
    | ~ spl5_16
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f418,f171,f212,f423])).

fof(f418,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl5_9 ),
    inference(resolution,[],[f86,f173])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f333,plain,
    ( spl5_32
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f325,f222,f330])).

fof(f325,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl5_17 ),
    inference(resolution,[],[f113,f224])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f301,plain,
    ( spl5_28
    | ~ spl5_16
    | ~ spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f295,f151,f171,f212,f298])).

fof(f295,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f85,f153])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f256,plain,
    ( spl5_21
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f251,f190,f185,f156,f253])).

fof(f156,plain,
    ( spl5_6
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f185,plain,
    ( spl5_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f190,plain,
    ( spl5_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f251,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f250,f187])).

fof(f187,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f185])).

fof(f250,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f158,f192])).

fof(f192,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f158,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f245,plain,
    ( spl5_20
    | ~ spl5_16
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f216,f171,f212,f242])).

fof(f216,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_9 ),
    inference(resolution,[],[f89,f173])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f240,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f237,f95])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f237,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl5_19
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f238,plain,
    ( spl5_16
    | ~ spl5_19
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f233,f222,f235,f212])).

fof(f233,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f81,f224])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f225,plain,
    ( spl5_17
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f220,f190,f185,f161,f222])).

fof(f161,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f220,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f219,f187])).

fof(f219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f163,f192])).

fof(f163,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f215,plain,
    ( spl5_15
    | ~ spl5_16
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f206,f171,f212,f208])).

fof(f206,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_9 ),
    inference(resolution,[],[f88,f173])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f205,plain,
    ( spl5_14
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f200,f196,f190,f202])).

fof(f196,plain,
    ( spl5_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f200,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f198,f192])).

fof(f198,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl5_13
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f194,f185,f166,f196])).

fof(f166,plain,
    ( spl5_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f194,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f168,f187])).

fof(f168,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f193,plain,
    ( spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f183,f136,f190])).

fof(f183,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f78,f138])).

fof(f138,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f188,plain,
    ( spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f182,f131,f185])).

fof(f131,plain,
    ( spl5_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f182,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f78,f133])).

fof(f133,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f174,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f65,f171])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
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

fof(f169,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f66,f166])).

fof(f66,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f164,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f67,f161])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f159,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f68,f156])).

fof(f68,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f154,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f69,f151])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f149,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f70,f146])).

fof(f146,plain,
    ( spl5_4
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f144,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f71,f141])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f72,f136])).

fof(f72,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f134,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f73,f131])).

fof(f73,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3130)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (3131)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (3134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (3132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (3143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (3158)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.53  % (3138)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.53  % (3154)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.53  % (3142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (3136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (3135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (3153)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.54  % (3145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.54  % (3139)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.54  % (3157)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.54  % (3137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.54  % (3155)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (3133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (3151)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (3144)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.55  % (3148)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (3147)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (3147)Refutation not found, incomplete strategy% (3147)------------------------------
% 1.38/0.55  % (3147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (3147)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (3147)Memory used [KB]: 10746
% 1.38/0.55  % (3147)Time elapsed: 0.129 s
% 1.38/0.55  % (3147)------------------------------
% 1.38/0.55  % (3147)------------------------------
% 1.38/0.55  % (3152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (3156)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (3140)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.55  % (3159)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (3149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.56  % (3141)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (3150)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.56  % (3141)Refutation not found, incomplete strategy% (3141)------------------------------
% 1.38/0.56  % (3141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (3141)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (3141)Memory used [KB]: 10746
% 1.38/0.56  % (3141)Time elapsed: 0.152 s
% 1.38/0.56  % (3141)------------------------------
% 1.38/0.56  % (3141)------------------------------
% 1.38/0.56  % (3146)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.58  % (3140)Refutation not found, incomplete strategy% (3140)------------------------------
% 1.38/0.58  % (3140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (3140)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (3140)Memory used [KB]: 10874
% 1.38/0.58  % (3140)Time elapsed: 0.147 s
% 1.38/0.58  % (3140)------------------------------
% 1.38/0.58  % (3140)------------------------------
% 1.38/0.60  % (3132)Refutation not found, incomplete strategy% (3132)------------------------------
% 1.38/0.60  % (3132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.60  % (3132)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.60  
% 1.38/0.60  % (3132)Memory used [KB]: 11513
% 1.38/0.60  % (3132)Time elapsed: 0.172 s
% 1.38/0.60  % (3132)------------------------------
% 1.38/0.60  % (3132)------------------------------
% 1.38/0.63  % (3146)Refutation found. Thanks to Tanya!
% 1.38/0.63  % SZS status Theorem for theBenchmark
% 1.38/0.63  % SZS output start Proof for theBenchmark
% 1.91/0.63  fof(f1841,plain,(
% 1.91/0.63    $false),
% 1.91/0.63    inference(avatar_sat_refutation,[],[f134,f139,f144,f149,f154,f159,f164,f169,f174,f188,f193,f199,f205,f215,f225,f238,f240,f245,f256,f301,f333,f426,f454,f477,f488,f515,f541,f594,f633,f676,f688,f690,f701,f733,f738,f743,f825,f878,f917,f1139,f1149,f1154,f1160,f1184,f1540,f1807,f1822,f1840])).
% 1.91/0.63  fof(f1840,plain,(
% 1.91/0.63    k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.91/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.91/0.63  fof(f1822,plain,(
% 1.91/0.63    ~spl5_28 | ~spl5_222 | ~spl5_20 | ~spl5_143 | spl5_224 | ~spl5_144 | ~spl5_188),
% 1.91/0.63    inference(avatar_split_clause,[],[f1817,f1537,f1151,f1819,f1146,f242,f1804,f298])).
% 1.91/0.63  fof(f298,plain,(
% 1.91/0.63    spl5_28 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.91/0.63  fof(f1804,plain,(
% 1.91/0.63    spl5_222 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).
% 1.91/0.63  fof(f242,plain,(
% 1.91/0.63    spl5_20 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.91/0.63  fof(f1146,plain,(
% 1.91/0.63    spl5_143 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).
% 1.91/0.63  fof(f1819,plain,(
% 1.91/0.63    spl5_224 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).
% 1.91/0.63  fof(f1151,plain,(
% 1.91/0.63    spl5_144 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).
% 1.91/0.63  fof(f1537,plain,(
% 1.91/0.63    spl5_188 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).
% 1.91/0.63  fof(f1817,plain,(
% 1.91/0.63    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl5_144 | ~spl5_188)),
% 1.91/0.63    inference(forward_demodulation,[],[f1794,f1539])).
% 1.91/0.63  fof(f1539,plain,(
% 1.91/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl5_188),
% 1.91/0.63    inference(avatar_component_clause,[],[f1537])).
% 1.91/0.63  fof(f1794,plain,(
% 1.91/0.63    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl5_144),
% 1.91/0.63    inference(resolution,[],[f1153,f118])).
% 1.91/0.63  fof(f118,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f60])).
% 1.91/0.63  fof(f60,plain,(
% 1.91/0.63    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.63    inference(flattening,[],[f59])).
% 1.91/0.63  fof(f59,plain,(
% 1.91/0.63    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.63    inference(ennf_transformation,[],[f27])).
% 1.91/0.63  fof(f27,axiom,(
% 1.91/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.91/0.63  fof(f1153,plain,(
% 1.91/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl5_144),
% 1.91/0.63    inference(avatar_component_clause,[],[f1151])).
% 1.91/0.63  fof(f1807,plain,(
% 1.91/0.63    spl5_222 | ~spl5_63 | ~spl5_144),
% 1.91/0.63    inference(avatar_split_clause,[],[f1802,f1151,f538,f1804])).
% 1.91/0.63  fof(f538,plain,(
% 1.91/0.63    spl5_63 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 1.91/0.63  fof(f1802,plain,(
% 1.91/0.63    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl5_63 | ~spl5_144)),
% 1.91/0.63    inference(forward_demodulation,[],[f1788,f540])).
% 1.91/0.63  fof(f540,plain,(
% 1.91/0.63    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl5_63),
% 1.91/0.63    inference(avatar_component_clause,[],[f538])).
% 1.91/0.63  fof(f1788,plain,(
% 1.91/0.63    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl5_144),
% 1.91/0.63    inference(resolution,[],[f1153,f112])).
% 1.91/0.63  fof(f112,plain,(
% 1.91/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.91/0.63    inference(cnf_transformation,[],[f55])).
% 1.91/0.63  fof(f55,plain,(
% 1.91/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.63    inference(ennf_transformation,[],[f16])).
% 1.91/0.63  fof(f16,axiom,(
% 1.91/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.91/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.91/0.63  fof(f1540,plain,(
% 1.91/0.63    ~spl5_15 | ~spl5_20 | spl5_188 | ~spl5_28 | ~spl5_59 | ~spl5_63 | ~spl5_100 | ~spl5_109),
% 1.91/0.63    inference(avatar_split_clause,[],[f1535,f894,f823,f538,f512,f298,f1537,f242,f208])).
% 1.91/0.63  fof(f208,plain,(
% 1.91/0.63    spl5_15 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.91/0.63  fof(f512,plain,(
% 1.91/0.63    spl5_59 <=> k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 1.91/0.63  fof(f823,plain,(
% 1.91/0.63    spl5_100 <=> ! [X0] : (~v1_funct_1(X0) | k2_funct_1(X0) = sK2 | k6_partfun1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 1.91/0.63  fof(f894,plain,(
% 1.91/0.63    spl5_109 <=> k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.91/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 1.91/0.63  fof(f1535,plain,(
% 1.91/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_28 | ~spl5_59 | ~spl5_63 | ~spl5_100 | ~spl5_109)),
% 1.91/0.63    inference(trivial_inequality_removal,[],[f1534])).
% 1.91/0.63  fof(f1534,plain,(
% 1.91/0.63    k2_relat_1(sK2) != k2_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_28 | ~spl5_59 | ~spl5_63 | ~spl5_100 | ~spl5_109)),
% 1.91/0.63    inference(forward_demodulation,[],[f1533,f514])).
% 1.91/0.63  fof(f514,plain,(
% 1.91/0.63    k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) | ~spl5_59),
% 1.91/0.63    inference(avatar_component_clause,[],[f512])).
% 1.91/0.63  fof(f1533,plain,(
% 1.91/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_28 | ~spl5_63 | ~spl5_100 | ~spl5_109)),
% 1.91/0.63    inference(trivial_inequality_removal,[],[f1532])).
% 1.91/0.63  fof(f1532,plain,(
% 1.91/0.63    k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_28 | ~spl5_63 | ~spl5_100 | ~spl5_109)),
% 1.91/0.63    inference(forward_demodulation,[],[f1531,f896])).
% 1.91/0.63  fof(f896,plain,(
% 1.91/0.63    k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl5_109),
% 1.91/0.63    inference(avatar_component_clause,[],[f894])).
% 1.91/0.63  fof(f1531,plain,(
% 1.91/0.63    k6_partfun1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_28 | ~spl5_63 | ~spl5_100)),
% 1.91/0.63    inference(forward_demodulation,[],[f1513,f540])).
% 1.91/0.63  fof(f1513,plain,(
% 1.91/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_28 | ~spl5_100)),
% 1.91/0.63    inference(resolution,[],[f824,f300])).
% 1.91/0.63  fof(f300,plain,(
% 1.91/0.63    v2_funct_1(k2_funct_1(sK2)) | ~spl5_28),
% 1.91/0.63    inference(avatar_component_clause,[],[f298])).
% 1.91/0.63  fof(f824,plain,(
% 1.91/0.63    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | k6_partfun1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_100),
% 1.91/0.63    inference(avatar_component_clause,[],[f823])).
% 1.91/0.63  fof(f1184,plain,(
% 1.91/0.63    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK1)),
% 1.91/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.91/0.63  fof(f1160,plain,(
% 1.91/0.63    spl5_109 | spl5_43 | ~spl5_5 | ~spl5_141 | ~spl5_9 | ~spl5_45 | ~spl5_55),
% 1.91/0.63    inference(avatar_split_clause,[],[f1129,f485,f423,f171,f1136,f151,f395,f894])).
% 1.91/0.65  fof(f395,plain,(
% 1.91/0.65    spl5_43 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.91/0.65  fof(f151,plain,(
% 1.91/0.65    spl5_5 <=> v2_funct_1(sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.91/0.65  fof(f1136,plain,(
% 1.91/0.65    spl5_141 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).
% 1.91/0.65  fof(f171,plain,(
% 1.91/0.65    spl5_9 <=> v1_funct_1(sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.91/0.65  fof(f423,plain,(
% 1.91/0.65    spl5_45 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.91/0.65  fof(f485,plain,(
% 1.91/0.65    spl5_55 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.91/0.65  fof(f1129,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl5_55),
% 1.91/0.65    inference(resolution,[],[f487,f119])).
% 1.91/0.65  fof(f119,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f62])).
% 1.91/0.65  fof(f62,plain,(
% 1.91/0.65    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.65    inference(flattening,[],[f61])).
% 1.91/0.65  fof(f61,plain,(
% 1.91/0.65    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.65    inference(ennf_transformation,[],[f23])).
% 1.91/0.65  fof(f23,axiom,(
% 1.91/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.91/0.65  fof(f487,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl5_55),
% 1.91/0.65    inference(avatar_component_clause,[],[f485])).
% 1.91/0.65  fof(f1154,plain,(
% 1.91/0.65    spl5_144 | ~spl5_141 | ~spl5_5 | ~spl5_9 | ~spl5_45 | ~spl5_55),
% 1.91/0.65    inference(avatar_split_clause,[],[f1127,f485,f423,f171,f151,f1136,f1151])).
% 1.91/0.65  fof(f1127,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl5_55),
% 1.91/0.65    inference(resolution,[],[f487,f117])).
% 1.91/0.65  fof(f117,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f58])).
% 1.91/0.65  fof(f58,plain,(
% 1.91/0.65    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.65    inference(flattening,[],[f57])).
% 1.91/0.65  fof(f57,plain,(
% 1.91/0.65    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.65    inference(ennf_transformation,[],[f22])).
% 1.91/0.65  fof(f22,axiom,(
% 1.91/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.91/0.65  fof(f1149,plain,(
% 1.91/0.65    spl5_143 | ~spl5_141 | ~spl5_5 | ~spl5_9 | ~spl5_45 | ~spl5_55),
% 1.91/0.65    inference(avatar_split_clause,[],[f1126,f485,f423,f171,f151,f1136,f1146])).
% 1.91/0.65  fof(f1126,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl5_55),
% 1.91/0.65    inference(resolution,[],[f487,f116])).
% 1.91/0.65  fof(f116,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f58])).
% 1.91/0.65  fof(f1139,plain,(
% 1.91/0.65    spl5_141 | ~spl5_55),
% 1.91/0.65    inference(avatar_split_clause,[],[f1122,f485,f1136])).
% 1.91/0.65  fof(f1122,plain,(
% 1.91/0.65    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl5_55),
% 1.91/0.65    inference(resolution,[],[f487,f112])).
% 1.91/0.65  fof(f917,plain,(
% 1.91/0.65    k1_xboole_0 != k2_struct_0(sK1) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 1.91/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.91/0.65  fof(f878,plain,(
% 1.91/0.65    spl5_107 | ~spl5_5 | ~spl5_9 | ~spl5_87 | ~spl5_88 | ~spl5_89),
% 1.91/0.65    inference(avatar_split_clause,[],[f873,f740,f735,f730,f171,f151,f875])).
% 1.91/0.65  fof(f875,plain,(
% 1.91/0.65    spl5_107 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 1.91/0.65  fof(f730,plain,(
% 1.91/0.65    spl5_87 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 1.91/0.65  fof(f735,plain,(
% 1.91/0.65    spl5_88 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 1.91/0.65  fof(f740,plain,(
% 1.91/0.65    spl5_89 <=> k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 1.91/0.65  fof(f873,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl5_88 | ~spl5_89)),
% 1.91/0.65    inference(trivial_inequality_removal,[],[f872])).
% 1.91/0.65  fof(f872,plain,(
% 1.91/0.65    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl5_88 | ~spl5_89)),
% 1.91/0.65    inference(forward_demodulation,[],[f868,f742])).
% 1.91/0.65  fof(f742,plain,(
% 1.91/0.65    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~spl5_89),
% 1.91/0.65    inference(avatar_component_clause,[],[f740])).
% 1.91/0.65  fof(f868,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~spl5_88),
% 1.91/0.65    inference(resolution,[],[f118,f737])).
% 1.91/0.65  fof(f737,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~spl5_88),
% 1.91/0.65    inference(avatar_component_clause,[],[f735])).
% 1.91/0.65  fof(f825,plain,(
% 1.91/0.65    ~spl5_16 | spl5_100 | ~spl5_9),
% 1.91/0.65    inference(avatar_split_clause,[],[f818,f171,f823,f212])).
% 1.91/0.65  fof(f212,plain,(
% 1.91/0.65    spl5_16 <=> v1_relat_1(sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.91/0.65  fof(f818,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK2) | k6_partfun1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k2_funct_1(X0) = sK2) ) | ~spl5_9),
% 1.91/0.65    inference(resolution,[],[f124,f173])).
% 1.91/0.65  fof(f173,plain,(
% 1.91/0.65    v1_funct_1(sK2) | ~spl5_9),
% 1.91/0.65    inference(avatar_component_clause,[],[f171])).
% 1.91/0.65  fof(f124,plain,(
% 1.91/0.65    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.91/0.65    inference(definition_unfolding,[],[f92,f75])).
% 1.91/0.65  fof(f75,plain,(
% 1.91/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f20])).
% 1.91/0.65  fof(f20,axiom,(
% 1.91/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.91/0.65  fof(f92,plain,(
% 1.91/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.91/0.65    inference(cnf_transformation,[],[f46])).
% 1.91/0.65  fof(f46,plain,(
% 1.91/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.65    inference(flattening,[],[f45])).
% 1.91/0.65  fof(f45,plain,(
% 1.91/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.65    inference(ennf_transformation,[],[f13])).
% 1.91/0.65  fof(f13,axiom,(
% 1.91/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.91/0.65  fof(f743,plain,(
% 1.91/0.65    spl5_89 | ~spl5_21 | ~spl5_83),
% 1.91/0.65    inference(avatar_split_clause,[],[f717,f683,f253,f740])).
% 1.91/0.65  fof(f253,plain,(
% 1.91/0.65    spl5_21 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.91/0.65  fof(f683,plain,(
% 1.91/0.65    spl5_83 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 1.91/0.65  fof(f717,plain,(
% 1.91/0.65    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl5_21 | ~spl5_83)),
% 1.91/0.65    inference(backward_demodulation,[],[f255,f685])).
% 1.91/0.65  fof(f685,plain,(
% 1.91/0.65    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl5_83),
% 1.91/0.65    inference(avatar_component_clause,[],[f683])).
% 1.91/0.65  fof(f255,plain,(
% 1.91/0.65    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl5_21),
% 1.91/0.65    inference(avatar_component_clause,[],[f253])).
% 1.91/0.65  fof(f738,plain,(
% 1.91/0.65    spl5_88 | ~spl5_17 | ~spl5_83),
% 1.91/0.65    inference(avatar_split_clause,[],[f716,f683,f222,f735])).
% 1.91/0.65  fof(f222,plain,(
% 1.91/0.65    spl5_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.91/0.65  fof(f716,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl5_17 | ~spl5_83)),
% 1.91/0.65    inference(backward_demodulation,[],[f224,f685])).
% 1.91/0.65  fof(f224,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl5_17),
% 1.91/0.65    inference(avatar_component_clause,[],[f222])).
% 1.91/0.65  fof(f733,plain,(
% 1.91/0.65    spl5_87 | ~spl5_14 | ~spl5_83),
% 1.91/0.65    inference(avatar_split_clause,[],[f715,f683,f202,f730])).
% 1.91/0.65  fof(f202,plain,(
% 1.91/0.65    spl5_14 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.91/0.65  fof(f715,plain,(
% 1.91/0.65    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | (~spl5_14 | ~spl5_83)),
% 1.91/0.65    inference(backward_demodulation,[],[f204,f685])).
% 1.91/0.65  fof(f204,plain,(
% 1.91/0.65    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl5_14),
% 1.91/0.65    inference(avatar_component_clause,[],[f202])).
% 1.91/0.65  fof(f701,plain,(
% 1.91/0.65    spl5_78 | spl5_84 | ~spl5_9 | ~spl5_14 | ~spl5_17),
% 1.91/0.65    inference(avatar_split_clause,[],[f693,f222,f202,f171,f698,f630])).
% 1.91/0.65  fof(f630,plain,(
% 1.91/0.65    spl5_78 <=> sP4(k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 1.91/0.65  fof(f698,plain,(
% 1.91/0.65    spl5_84 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 1.91/0.65  fof(f693,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) | sP4(k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl5_17),
% 1.91/0.65    inference(resolution,[],[f128,f224])).
% 1.91/0.65  fof(f128,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | r2_funct_2(X0,X1,X2,X2) | sP4(X1,X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f128_D])).
% 1.91/0.65  fof(f128_D,plain,(
% 1.91/0.65    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | r2_funct_2(X0,X1,X2,X2)) ) <=> ~sP4(X1,X0)) )),
% 1.91/0.65    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 1.91/0.65  fof(f690,plain,(
% 1.91/0.65    ~spl5_16 | spl5_83 | ~spl5_32 | ~spl5_81),
% 1.91/0.65    inference(avatar_split_clause,[],[f689,f669,f330,f683,f212])).
% 1.91/0.65  fof(f330,plain,(
% 1.91/0.65    spl5_32 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.91/0.65  fof(f669,plain,(
% 1.91/0.65    spl5_81 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 1.91/0.65  fof(f689,plain,(
% 1.91/0.65    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl5_81),
% 1.91/0.65    inference(resolution,[],[f671,f101])).
% 1.91/0.65  fof(f101,plain,(
% 1.91/0.65    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f54])).
% 1.91/0.65  fof(f54,plain,(
% 1.91/0.65    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.91/0.65    inference(flattening,[],[f53])).
% 1.91/0.65  fof(f53,plain,(
% 1.91/0.65    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.91/0.65    inference(ennf_transformation,[],[f18])).
% 1.91/0.65  fof(f18,axiom,(
% 1.91/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.91/0.65  fof(f671,plain,(
% 1.91/0.65    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl5_81),
% 1.91/0.65    inference(avatar_component_clause,[],[f669])).
% 1.91/0.65  fof(f688,plain,(
% 1.91/0.65    spl5_3 | ~spl5_2 | ~spl5_82),
% 1.91/0.65    inference(avatar_split_clause,[],[f687,f673,f136,f141])).
% 1.91/0.65  fof(f141,plain,(
% 1.91/0.65    spl5_3 <=> v2_struct_0(sK1)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.91/0.65  fof(f136,plain,(
% 1.91/0.65    spl5_2 <=> l1_struct_0(sK1)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.91/0.65  fof(f673,plain,(
% 1.91/0.65    spl5_82 <=> v1_xboole_0(k2_struct_0(sK1))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 1.91/0.65  fof(f687,plain,(
% 1.91/0.65    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_82),
% 1.91/0.65    inference(resolution,[],[f675,f82])).
% 1.91/0.65  fof(f82,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f36])).
% 1.91/0.65  fof(f36,plain,(
% 1.91/0.65    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.91/0.65    inference(flattening,[],[f35])).
% 1.91/0.65  fof(f35,plain,(
% 1.91/0.65    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.91/0.65    inference(ennf_transformation,[],[f26])).
% 1.91/0.65  fof(f26,axiom,(
% 1.91/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.91/0.65  fof(f675,plain,(
% 1.91/0.65    v1_xboole_0(k2_struct_0(sK1)) | ~spl5_82),
% 1.91/0.65    inference(avatar_component_clause,[],[f673])).
% 1.91/0.65  fof(f676,plain,(
% 1.91/0.65    spl5_81 | ~spl5_14 | ~spl5_9 | spl5_82 | ~spl5_17),
% 1.91/0.65    inference(avatar_split_clause,[],[f664,f222,f673,f171,f202,f669])).
% 1.91/0.65  fof(f664,plain,(
% 1.91/0.65    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl5_17),
% 1.91/0.65    inference(resolution,[],[f96,f224])).
% 1.91/0.65  fof(f96,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f50])).
% 1.91/0.65  fof(f50,plain,(
% 1.91/0.65    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.91/0.65    inference(flattening,[],[f49])).
% 1.91/0.65  fof(f49,plain,(
% 1.91/0.65    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.91/0.65    inference(ennf_transformation,[],[f17])).
% 1.91/0.65  fof(f17,axiom,(
% 1.91/0.65    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.91/0.65  fof(f633,plain,(
% 1.91/0.65    ~spl5_78 | ~spl5_9 | ~spl5_14 | ~spl5_17),
% 1.91/0.65    inference(avatar_split_clause,[],[f609,f222,f202,f171,f630])).
% 1.91/0.65  fof(f609,plain,(
% 1.91/0.65    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~sP4(k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl5_17),
% 1.91/0.65    inference(resolution,[],[f129,f224])).
% 1.91/0.65  fof(f129,plain,(
% 1.91/0.65    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP4(X1,X0)) )),
% 1.91/0.65    inference(general_splitting,[],[f121,f128_D])).
% 1.91/0.65  fof(f121,plain,(
% 1.91/0.65    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f64])).
% 1.91/0.65  fof(f64,plain,(
% 1.91/0.65    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.91/0.65    inference(flattening,[],[f63])).
% 1.91/0.65  fof(f63,plain,(
% 1.91/0.65    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.91/0.65    inference(ennf_transformation,[],[f21])).
% 1.91/0.65  fof(f21,axiom,(
% 1.91/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.91/0.65  fof(f594,plain,(
% 1.91/0.65    spl5_71 | ~spl5_17),
% 1.91/0.65    inference(avatar_split_clause,[],[f586,f222,f591])).
% 1.91/0.65  fof(f591,plain,(
% 1.91/0.65    spl5_71 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 1.91/0.65  fof(f586,plain,(
% 1.91/0.65    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl5_17),
% 1.91/0.65    inference(resolution,[],[f112,f224])).
% 1.91/0.65  fof(f541,plain,(
% 1.91/0.65    spl5_63 | ~spl5_16 | ~spl5_9 | ~spl5_5),
% 1.91/0.65    inference(avatar_split_clause,[],[f532,f151,f171,f212,f538])).
% 1.91/0.65  fof(f532,plain,(
% 1.91/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl5_5),
% 1.91/0.65    inference(resolution,[],[f91,f153])).
% 1.91/0.65  fof(f153,plain,(
% 1.91/0.65    v2_funct_1(sK2) | ~spl5_5),
% 1.91/0.65    inference(avatar_component_clause,[],[f151])).
% 1.91/0.65  fof(f91,plain,(
% 1.91/0.65    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f44])).
% 1.91/0.65  fof(f44,plain,(
% 1.91/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.65    inference(flattening,[],[f43])).
% 1.91/0.65  fof(f43,plain,(
% 1.91/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.65    inference(ennf_transformation,[],[f12])).
% 1.91/0.65  fof(f12,axiom,(
% 1.91/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.91/0.65  fof(f515,plain,(
% 1.91/0.65    spl5_59 | ~spl5_16 | ~spl5_9 | ~spl5_5),
% 1.91/0.65    inference(avatar_split_clause,[],[f506,f151,f171,f212,f512])).
% 1.91/0.65  fof(f506,plain,(
% 1.91/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) | ~spl5_5),
% 1.91/0.65    inference(resolution,[],[f90,f153])).
% 1.91/0.65  fof(f90,plain,(
% 1.91/0.65    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f44])).
% 1.91/0.65  fof(f488,plain,(
% 1.91/0.65    spl5_55 | ~spl5_16 | ~spl5_9),
% 1.91/0.65    inference(avatar_split_clause,[],[f480,f171,f212,f485])).
% 1.91/0.65  fof(f480,plain,(
% 1.91/0.65    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl5_9),
% 1.91/0.65    inference(resolution,[],[f87,f173])).
% 1.91/0.65  fof(f87,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f40])).
% 1.91/0.65  fof(f40,plain,(
% 1.91/0.65    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.65    inference(flattening,[],[f39])).
% 1.91/0.65  fof(f39,plain,(
% 1.91/0.65    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.65    inference(ennf_transformation,[],[f24])).
% 1.91/0.65  fof(f24,axiom,(
% 1.91/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.91/0.65  fof(f477,plain,(
% 1.91/0.65    ~spl5_50),
% 1.91/0.65    inference(avatar_contradiction_clause,[],[f476])).
% 1.91/0.65  fof(f476,plain,(
% 1.91/0.65    $false | ~spl5_50),
% 1.91/0.65    inference(resolution,[],[f453,f108])).
% 1.91/0.65  fof(f108,plain,(
% 1.91/0.65    ( ! [X0,X1] : (v1_xboole_0(sK3(X0,X1))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f19])).
% 1.91/0.65  fof(f19,axiom,(
% 1.91/0.65    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).
% 1.91/0.65  fof(f453,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl5_50),
% 1.91/0.65    inference(avatar_component_clause,[],[f452])).
% 1.91/0.65  fof(f452,plain,(
% 1.91/0.65    spl5_50 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.91/0.65  fof(f454,plain,(
% 1.91/0.65    spl5_49 | spl5_50),
% 1.91/0.65    inference(avatar_split_clause,[],[f442,f452,f448])).
% 1.91/0.65  fof(f448,plain,(
% 1.91/0.65    spl5_49 <=> v1_xboole_0(k1_xboole_0)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.91/0.65  fof(f442,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_xboole_0)) )),
% 1.91/0.65    inference(resolution,[],[f97,f217])).
% 1.91/0.65  fof(f217,plain,(
% 1.91/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.91/0.65    inference(resolution,[],[f102,f74])).
% 1.91/0.65  fof(f74,plain,(
% 1.91/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f1])).
% 1.91/0.65  fof(f1,axiom,(
% 1.91/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.91/0.65  fof(f102,plain,(
% 1.91/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f3])).
% 1.91/0.65  fof(f3,axiom,(
% 1.91/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.91/0.65  fof(f97,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f51])).
% 1.91/0.65  fof(f51,plain,(
% 1.91/0.65    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.91/0.65    inference(ennf_transformation,[],[f15])).
% 1.91/0.65  fof(f15,axiom,(
% 1.91/0.65    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.91/0.65  fof(f426,plain,(
% 1.91/0.65    spl5_45 | ~spl5_16 | ~spl5_9),
% 1.91/0.65    inference(avatar_split_clause,[],[f418,f171,f212,f423])).
% 1.91/0.65  fof(f418,plain,(
% 1.91/0.65    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl5_9),
% 1.91/0.65    inference(resolution,[],[f86,f173])).
% 1.91/0.65  fof(f86,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f40])).
% 1.91/0.65  fof(f333,plain,(
% 1.91/0.65    spl5_32 | ~spl5_17),
% 1.91/0.65    inference(avatar_split_clause,[],[f325,f222,f330])).
% 1.91/0.65  fof(f325,plain,(
% 1.91/0.65    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl5_17),
% 1.91/0.65    inference(resolution,[],[f113,f224])).
% 1.91/0.65  fof(f113,plain,(
% 1.91/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f56])).
% 1.91/0.65  fof(f56,plain,(
% 1.91/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.65    inference(ennf_transformation,[],[f14])).
% 1.91/0.65  fof(f14,axiom,(
% 1.91/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.91/0.65  fof(f301,plain,(
% 1.91/0.65    spl5_28 | ~spl5_16 | ~spl5_9 | ~spl5_5),
% 1.91/0.65    inference(avatar_split_clause,[],[f295,f151,f171,f212,f298])).
% 1.91/0.65  fof(f295,plain,(
% 1.91/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~spl5_5),
% 1.91/0.65    inference(resolution,[],[f85,f153])).
% 1.91/0.65  fof(f85,plain,(
% 1.91/0.65    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f38])).
% 1.91/0.65  fof(f38,plain,(
% 1.91/0.65    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.65    inference(flattening,[],[f37])).
% 1.91/0.65  fof(f37,plain,(
% 1.91/0.65    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.65    inference(ennf_transformation,[],[f10])).
% 1.91/0.65  fof(f10,axiom,(
% 1.91/0.65    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.91/0.65  fof(f256,plain,(
% 1.91/0.65    spl5_21 | ~spl5_6 | ~spl5_11 | ~spl5_12),
% 1.91/0.65    inference(avatar_split_clause,[],[f251,f190,f185,f156,f253])).
% 1.91/0.65  fof(f156,plain,(
% 1.91/0.65    spl5_6 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.91/0.65  fof(f185,plain,(
% 1.91/0.65    spl5_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.91/0.65  fof(f190,plain,(
% 1.91/0.65    spl5_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.91/0.65  fof(f251,plain,(
% 1.91/0.65    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl5_6 | ~spl5_11 | ~spl5_12)),
% 1.91/0.65    inference(forward_demodulation,[],[f250,f187])).
% 1.91/0.65  fof(f187,plain,(
% 1.91/0.65    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_11),
% 1.91/0.65    inference(avatar_component_clause,[],[f185])).
% 1.91/0.65  fof(f250,plain,(
% 1.91/0.65    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl5_6 | ~spl5_12)),
% 1.91/0.65    inference(forward_demodulation,[],[f158,f192])).
% 1.91/0.65  fof(f192,plain,(
% 1.91/0.65    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl5_12),
% 1.91/0.65    inference(avatar_component_clause,[],[f190])).
% 1.91/0.65  fof(f158,plain,(
% 1.91/0.65    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~spl5_6),
% 1.91/0.65    inference(avatar_component_clause,[],[f156])).
% 1.91/0.65  fof(f245,plain,(
% 1.91/0.65    spl5_20 | ~spl5_16 | ~spl5_9),
% 1.91/0.65    inference(avatar_split_clause,[],[f216,f171,f212,f242])).
% 1.91/0.65  fof(f216,plain,(
% 1.91/0.65    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl5_9),
% 1.91/0.65    inference(resolution,[],[f89,f173])).
% 1.91/0.65  fof(f89,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f42])).
% 1.91/0.65  fof(f42,plain,(
% 1.91/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.65    inference(flattening,[],[f41])).
% 1.91/0.65  fof(f41,plain,(
% 1.91/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.65    inference(ennf_transformation,[],[f8])).
% 1.91/0.65  fof(f8,axiom,(
% 1.91/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.91/0.65  fof(f240,plain,(
% 1.91/0.65    spl5_19),
% 1.91/0.65    inference(avatar_contradiction_clause,[],[f239])).
% 1.91/0.65  fof(f239,plain,(
% 1.91/0.65    $false | spl5_19),
% 1.91/0.65    inference(resolution,[],[f237,f95])).
% 1.91/0.65  fof(f95,plain,(
% 1.91/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f6])).
% 1.91/0.65  fof(f6,axiom,(
% 1.91/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.91/0.65  fof(f237,plain,(
% 1.91/0.65    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl5_19),
% 1.91/0.65    inference(avatar_component_clause,[],[f235])).
% 1.91/0.65  fof(f235,plain,(
% 1.91/0.65    spl5_19 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.91/0.65  fof(f238,plain,(
% 1.91/0.65    spl5_16 | ~spl5_19 | ~spl5_17),
% 1.91/0.65    inference(avatar_split_clause,[],[f233,f222,f235,f212])).
% 1.91/0.65  fof(f233,plain,(
% 1.91/0.65    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2) | ~spl5_17),
% 1.91/0.65    inference(resolution,[],[f81,f224])).
% 1.91/0.65  fof(f81,plain,(
% 1.91/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f34])).
% 1.91/0.65  fof(f34,plain,(
% 1.91/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.91/0.65    inference(ennf_transformation,[],[f4])).
% 1.91/0.65  fof(f4,axiom,(
% 1.91/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.91/0.65  fof(f225,plain,(
% 1.91/0.65    spl5_17 | ~spl5_7 | ~spl5_11 | ~spl5_12),
% 1.91/0.65    inference(avatar_split_clause,[],[f220,f190,f185,f161,f222])).
% 1.91/0.65  fof(f161,plain,(
% 1.91/0.65    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.91/0.65  fof(f220,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl5_7 | ~spl5_11 | ~spl5_12)),
% 1.91/0.65    inference(forward_demodulation,[],[f219,f187])).
% 1.91/0.65  fof(f219,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl5_7 | ~spl5_12)),
% 1.91/0.65    inference(forward_demodulation,[],[f163,f192])).
% 1.91/0.65  fof(f163,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_7),
% 1.91/0.65    inference(avatar_component_clause,[],[f161])).
% 1.91/0.65  fof(f215,plain,(
% 1.91/0.65    spl5_15 | ~spl5_16 | ~spl5_9),
% 1.91/0.65    inference(avatar_split_clause,[],[f206,f171,f212,f208])).
% 1.91/0.65  fof(f206,plain,(
% 1.91/0.65    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl5_9),
% 1.91/0.65    inference(resolution,[],[f88,f173])).
% 1.91/0.65  fof(f88,plain,(
% 1.91/0.65    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.91/0.65    inference(cnf_transformation,[],[f42])).
% 1.91/0.65  fof(f205,plain,(
% 1.91/0.65    spl5_14 | ~spl5_12 | ~spl5_13),
% 1.91/0.65    inference(avatar_split_clause,[],[f200,f196,f190,f202])).
% 1.91/0.65  fof(f196,plain,(
% 1.91/0.65    spl5_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.91/0.65  fof(f200,plain,(
% 1.91/0.65    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl5_12 | ~spl5_13)),
% 1.91/0.65    inference(forward_demodulation,[],[f198,f192])).
% 1.91/0.65  fof(f198,plain,(
% 1.91/0.65    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_13),
% 1.91/0.65    inference(avatar_component_clause,[],[f196])).
% 1.91/0.65  fof(f199,plain,(
% 1.91/0.65    spl5_13 | ~spl5_8 | ~spl5_11),
% 1.91/0.65    inference(avatar_split_clause,[],[f194,f185,f166,f196])).
% 1.91/0.65  fof(f166,plain,(
% 1.91/0.65    spl5_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.91/0.65  fof(f194,plain,(
% 1.91/0.65    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_8 | ~spl5_11)),
% 1.91/0.65    inference(backward_demodulation,[],[f168,f187])).
% 1.91/0.65  fof(f168,plain,(
% 1.91/0.65    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_8),
% 1.91/0.65    inference(avatar_component_clause,[],[f166])).
% 1.91/0.65  fof(f193,plain,(
% 1.91/0.65    spl5_12 | ~spl5_2),
% 1.91/0.65    inference(avatar_split_clause,[],[f183,f136,f190])).
% 1.91/0.65  fof(f183,plain,(
% 1.91/0.65    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl5_2),
% 1.91/0.65    inference(resolution,[],[f78,f138])).
% 1.91/0.65  fof(f138,plain,(
% 1.91/0.65    l1_struct_0(sK1) | ~spl5_2),
% 1.91/0.65    inference(avatar_component_clause,[],[f136])).
% 1.91/0.65  fof(f78,plain,(
% 1.91/0.65    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.91/0.65    inference(cnf_transformation,[],[f32])).
% 1.91/0.65  fof(f32,plain,(
% 1.91/0.65    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.91/0.65    inference(ennf_transformation,[],[f25])).
% 1.91/0.65  fof(f25,axiom,(
% 1.91/0.65    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.91/0.65  fof(f188,plain,(
% 1.91/0.65    spl5_11 | ~spl5_1),
% 1.91/0.65    inference(avatar_split_clause,[],[f182,f131,f185])).
% 1.91/0.65  fof(f131,plain,(
% 1.91/0.65    spl5_1 <=> l1_struct_0(sK0)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.91/0.65  fof(f182,plain,(
% 1.91/0.65    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_1),
% 1.91/0.65    inference(resolution,[],[f78,f133])).
% 1.91/0.65  fof(f133,plain,(
% 1.91/0.65    l1_struct_0(sK0) | ~spl5_1),
% 1.91/0.65    inference(avatar_component_clause,[],[f131])).
% 1.91/0.65  fof(f174,plain,(
% 1.91/0.65    spl5_9),
% 1.91/0.65    inference(avatar_split_clause,[],[f65,f171])).
% 1.91/0.65  fof(f65,plain,(
% 1.91/0.65    v1_funct_1(sK2)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f31,plain,(
% 1.91/0.65    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.91/0.65    inference(flattening,[],[f30])).
% 1.91/0.65  fof(f30,plain,(
% 1.91/0.65    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.91/0.65    inference(ennf_transformation,[],[f29])).
% 1.91/0.65  fof(f29,negated_conjecture,(
% 1.91/0.65    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.91/0.65    inference(negated_conjecture,[],[f28])).
% 1.91/0.65  fof(f28,conjecture,(
% 1.91/0.65    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.91/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.91/0.65  fof(f169,plain,(
% 1.91/0.65    spl5_8),
% 1.91/0.65    inference(avatar_split_clause,[],[f66,f166])).
% 1.91/0.65  fof(f66,plain,(
% 1.91/0.65    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f164,plain,(
% 1.91/0.65    spl5_7),
% 1.91/0.65    inference(avatar_split_clause,[],[f67,f161])).
% 1.91/0.65  fof(f67,plain,(
% 1.91/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f159,plain,(
% 1.91/0.65    spl5_6),
% 1.91/0.65    inference(avatar_split_clause,[],[f68,f156])).
% 1.91/0.65  fof(f68,plain,(
% 1.91/0.65    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f154,plain,(
% 1.91/0.65    spl5_5),
% 1.91/0.65    inference(avatar_split_clause,[],[f69,f151])).
% 1.91/0.65  fof(f69,plain,(
% 1.91/0.65    v2_funct_1(sK2)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f149,plain,(
% 1.91/0.65    ~spl5_4),
% 1.91/0.65    inference(avatar_split_clause,[],[f70,f146])).
% 1.91/0.65  fof(f146,plain,(
% 1.91/0.65    spl5_4 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.91/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.91/0.65  fof(f70,plain,(
% 1.91/0.65    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f144,plain,(
% 1.91/0.65    ~spl5_3),
% 1.91/0.65    inference(avatar_split_clause,[],[f71,f141])).
% 1.91/0.65  fof(f71,plain,(
% 1.91/0.65    ~v2_struct_0(sK1)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f139,plain,(
% 1.91/0.65    spl5_2),
% 1.91/0.65    inference(avatar_split_clause,[],[f72,f136])).
% 1.91/0.65  fof(f72,plain,(
% 1.91/0.65    l1_struct_0(sK1)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  fof(f134,plain,(
% 1.91/0.65    spl5_1),
% 1.91/0.65    inference(avatar_split_clause,[],[f73,f131])).
% 1.91/0.65  fof(f73,plain,(
% 1.91/0.65    l1_struct_0(sK0)),
% 1.91/0.65    inference(cnf_transformation,[],[f31])).
% 1.91/0.65  % SZS output end Proof for theBenchmark
% 1.91/0.65  % (3146)------------------------------
% 1.91/0.65  % (3146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.65  % (3146)Termination reason: Refutation
% 1.91/0.65  
% 1.91/0.65  % (3146)Memory used [KB]: 12153
% 1.91/0.65  % (3146)Time elapsed: 0.219 s
% 1.91/0.65  % (3146)------------------------------
% 1.91/0.65  % (3146)------------------------------
% 1.91/0.65  % (3129)Success in time 0.282 s
%------------------------------------------------------------------------------
