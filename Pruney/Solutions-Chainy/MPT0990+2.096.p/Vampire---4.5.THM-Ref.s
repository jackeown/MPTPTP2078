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
% DateTime   : Thu Dec  3 13:02:45 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 396 expanded)
%              Number of leaves         :   48 ( 189 expanded)
%              Depth                    :   12
%              Number of atoms          :  786 (2246 expanded)
%              Number of equality atoms :  186 ( 683 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f127,f132,f142,f147,f152,f157,f166,f171,f191,f207,f227,f252,f266,f280,f306,f340,f351,f402,f410,f414,f415,f510,f522,f534,f557])).

fof(f557,plain,
    ( ~ spl5_14
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_2
    | ~ spl5_3
    | spl5_8
    | ~ spl5_18
    | ~ spl5_26
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f543,f531,f348,f277,f188,f129,f104,f99,f168,f94,f163])).

fof(f163,plain,
    ( spl5_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f94,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f168,plain,
    ( spl5_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f99,plain,
    ( spl5_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( spl5_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f129,plain,
    ( spl5_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f188,plain,
    ( spl5_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f277,plain,
    ( spl5_26
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f348,plain,
    ( spl5_39
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f531,plain,
    ( spl5_61
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f543,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_18
    | ~ spl5_26
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( sK0 != sK0
    | k2_funct_1(sK2) = sK3
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_18
    | ~ spl5_26
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f541,f350])).

fof(f350,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f348])).

fof(f541,plain,
    ( sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_18
    | ~ spl5_26
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f540,f279])).

fof(f279,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f277])).

fof(f540,plain,
    ( k2_funct_1(sK2) = sK3
    | k2_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_18
    | ~ spl5_61 ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k2_funct_1(sK2) = sK3
    | k2_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_18
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f538,f190])).

fof(f190,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f538,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k2_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_61 ),
    inference(superposition,[],[f83,f533])).

fof(f533,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f531])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f534,plain,
    ( spl5_61
    | ~ spl5_29
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f523,f507,f295,f531])).

fof(f295,plain,
    ( spl5_29
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f507,plain,
    ( spl5_60
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f523,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl5_29
    | ~ spl5_60 ),
    inference(superposition,[],[f509,f297])).

fof(f297,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f295])).

fof(f509,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f507])).

fof(f522,plain,
    ( ~ spl5_15
    | ~ spl5_2
    | ~ spl5_28
    | spl5_31
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f519,f507,f303,f291,f99,f168])).

fof(f291,plain,
    ( spl5_28
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f303,plain,
    ( spl5_31
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f519,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f514,f87])).

fof(f87,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f73])).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f514,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_60 ),
    inference(superposition,[],[f62,f509])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f510,plain,
    ( ~ spl5_2
    | ~ spl5_7
    | ~ spl5_11
    | spl5_60
    | ~ spl5_28
    | spl5_4
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f345,f337,f109,f291,f507,f144,f124,f99])).

fof(f124,plain,
    ( spl5_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f144,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f109,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f337,plain,
    ( spl5_38
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f345,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_38 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_38 ),
    inference(superposition,[],[f58,f339])).

fof(f339,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f337])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
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
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f415,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f414,plain,(
    spl5_49 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl5_49 ),
    inference(unit_resulting_resolution,[],[f84,f409])).

fof(f409,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_49 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl5_49
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f410,plain,
    ( spl5_28
    | spl5_4
    | ~ spl5_11
    | ~ spl5_7
    | ~ spl5_2
    | ~ spl5_49
    | ~ spl5_20
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f403,f400,f204,f407,f99,f124,f144,f109,f291])).

fof(f204,plain,
    ( spl5_20
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f400,plain,
    ( spl5_48
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f403,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl5_20
    | ~ spl5_48 ),
    inference(superposition,[],[f401,f206])).

fof(f206,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f401,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | k1_xboole_0 = X0
        | v2_funct_1(X1) )
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f400])).

fof(f402,plain,
    ( ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10
    | spl5_48
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f368,f149,f400,f139,f119,f94])).

fof(f119,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f139,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f149,plain,
    ( spl5_12
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f368,plain,
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
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f363])).

fof(f363,plain,
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
    | ~ spl5_12 ),
    inference(superposition,[],[f65,f151])).

fof(f151,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f351,plain,
    ( ~ spl5_11
    | spl5_39
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f341,f337,f348,f144])).

fof(f341,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_38 ),
    inference(superposition,[],[f339,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f340,plain,
    ( ~ spl5_2
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10
    | spl5_38
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f332,f154,f337,f139,f119,f94,f144,f124,f99])).

fof(f154,plain,
    ( spl5_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f332,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_13 ),
    inference(resolution,[],[f72,f156])).

fof(f156,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f306,plain,
    ( ~ spl5_15
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_1
    | ~ spl5_28
    | spl5_29
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_18
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f256,f239,f188,f303,f299,f295,f291,f94,f163,f99,f168])).

fof(f299,plain,
    ( spl5_30
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f239,plain,
    ( spl5_23
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f256,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_18
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f255,f190])).

fof(f255,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_23 ),
    inference(superposition,[],[f83,f241])).

fof(f241,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f239])).

fof(f280,plain,
    ( ~ spl5_14
    | ~ spl5_1
    | ~ spl5_3
    | spl5_26
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f270,f263,f277,f104,f94,f163])).

fof(f263,plain,
    ( spl5_25
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f270,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f267,f87])).

fof(f267,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_25 ),
    inference(superposition,[],[f62,f265])).

fof(f265,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f263])).

fof(f266,plain,
    ( ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10
    | spl5_25
    | ~ spl5_3
    | spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f246,f149,f114,f104,f263,f139,f119,f94])).

fof(f114,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f246,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f243])).

fof(f243,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_12 ),
    inference(superposition,[],[f58,f151])).

fof(f252,plain,
    ( ~ spl5_1
    | ~ spl5_10
    | ~ spl5_2
    | ~ spl5_11
    | spl5_23
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f228,f204,f239,f144,f99,f139,f94])).

fof(f228,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_20 ),
    inference(superposition,[],[f206,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f227,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f96,f101,f141,f146,f202,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f202,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl5_19
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f141,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f101,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f96,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f207,plain,
    ( ~ spl5_19
    | spl5_20
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f197,f154,f204,f200])).

fof(f197,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_13 ),
    inference(resolution,[],[f194,f156])).

fof(f194,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f70,f86])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f79,f73])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f191,plain,
    ( ~ spl5_10
    | spl5_18
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f185,f149,f188,f139])).

fof(f185,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_12 ),
    inference(superposition,[],[f77,f151])).

fof(f171,plain,
    ( spl5_15
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f160,f144,f168])).

fof(f160,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_11 ),
    inference(resolution,[],[f78,f146])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f166,plain,
    ( spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f159,f139,f163])).

fof(f159,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f78,f141])).

fof(f157,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f53,f154])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f152,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f52,f149])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f147,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f51,f144])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f142,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f48,f139])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f132,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f57,f129])).

fof(f57,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f127,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f50,f124])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f47,f119])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f56,f114])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f112,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f55,f109])).

fof(f55,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f54,f104])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (17424)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (17422)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.54  % (17416)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.54  % (17440)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.55  % (17419)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.55  % (17434)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.28/0.55  % (17432)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.28/0.55  % (17430)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.55  % (17437)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.55  % (17436)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.28/0.55  % (17443)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.55  % (17438)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.56  % (17439)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.56  % (17444)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.28/0.56  % (17429)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.28/0.56  % (17423)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.56  % (17426)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.28/0.56  % (17432)Refutation not found, incomplete strategy% (17432)------------------------------
% 1.28/0.56  % (17432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (17432)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.56  
% 1.28/0.56  % (17432)Memory used [KB]: 10746
% 1.28/0.56  % (17432)Time elapsed: 0.139 s
% 1.28/0.56  % (17432)------------------------------
% 1.28/0.56  % (17432)------------------------------
% 1.28/0.56  % (17427)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.56  % (17441)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.56  % (17425)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.56  % (17418)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.56  % (17421)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.56  % (17431)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.56  % (17420)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.57  % (17417)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.57  % (17445)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.57  % (17442)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.57  % (17428)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.58  % (17435)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.58  % (17433)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.58  % (17426)Refutation not found, incomplete strategy% (17426)------------------------------
% 1.28/0.58  % (17426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.58  % (17444)Refutation not found, incomplete strategy% (17444)------------------------------
% 1.28/0.58  % (17444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.58  % (17444)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.58  
% 1.28/0.58  % (17444)Memory used [KB]: 11001
% 1.28/0.58  % (17444)Time elapsed: 0.167 s
% 1.28/0.58  % (17444)------------------------------
% 1.28/0.58  % (17444)------------------------------
% 1.28/0.58  % (17426)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.58  
% 1.28/0.58  % (17426)Memory used [KB]: 11001
% 1.28/0.58  % (17426)Time elapsed: 0.142 s
% 1.28/0.58  % (17426)------------------------------
% 1.28/0.58  % (17426)------------------------------
% 1.28/0.59  % (17439)Refutation found. Thanks to Tanya!
% 1.28/0.59  % SZS status Theorem for theBenchmark
% 1.28/0.60  % SZS output start Proof for theBenchmark
% 1.28/0.60  fof(f558,plain,(
% 1.28/0.60    $false),
% 1.28/0.60    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f127,f132,f142,f147,f152,f157,f166,f171,f191,f207,f227,f252,f266,f280,f306,f340,f351,f402,f410,f414,f415,f510,f522,f534,f557])).
% 1.28/0.60  fof(f557,plain,(
% 1.28/0.60    ~spl5_14 | ~spl5_1 | ~spl5_15 | ~spl5_2 | ~spl5_3 | spl5_8 | ~spl5_18 | ~spl5_26 | ~spl5_39 | ~spl5_61),
% 1.28/0.60    inference(avatar_split_clause,[],[f543,f531,f348,f277,f188,f129,f104,f99,f168,f94,f163])).
% 1.28/0.60  fof(f163,plain,(
% 1.28/0.60    spl5_14 <=> v1_relat_1(sK2)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.28/0.60  fof(f94,plain,(
% 1.28/0.60    spl5_1 <=> v1_funct_1(sK2)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.28/0.60  fof(f168,plain,(
% 1.28/0.60    spl5_15 <=> v1_relat_1(sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.28/0.60  fof(f99,plain,(
% 1.28/0.60    spl5_2 <=> v1_funct_1(sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.28/0.60  fof(f104,plain,(
% 1.28/0.60    spl5_3 <=> v2_funct_1(sK2)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.28/0.60  fof(f129,plain,(
% 1.28/0.60    spl5_8 <=> k2_funct_1(sK2) = sK3),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.28/0.60  fof(f188,plain,(
% 1.28/0.60    spl5_18 <=> sK1 = k2_relat_1(sK2)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.28/0.60  fof(f277,plain,(
% 1.28/0.60    spl5_26 <=> sK0 = k1_relat_1(sK2)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.28/0.60  fof(f348,plain,(
% 1.28/0.60    spl5_39 <=> sK0 = k2_relat_1(sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.28/0.60  fof(f531,plain,(
% 1.28/0.60    spl5_61 <=> k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 1.28/0.60  fof(f543,plain,(
% 1.28/0.60    k2_funct_1(sK2) = sK3 | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_18 | ~spl5_26 | ~spl5_39 | ~spl5_61)),
% 1.28/0.60    inference(trivial_inequality_removal,[],[f542])).
% 1.28/0.60  fof(f542,plain,(
% 1.28/0.60    sK0 != sK0 | k2_funct_1(sK2) = sK3 | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_18 | ~spl5_26 | ~spl5_39 | ~spl5_61)),
% 1.28/0.60    inference(forward_demodulation,[],[f541,f350])).
% 1.28/0.60  fof(f350,plain,(
% 1.28/0.60    sK0 = k2_relat_1(sK3) | ~spl5_39),
% 1.28/0.60    inference(avatar_component_clause,[],[f348])).
% 1.28/0.60  fof(f541,plain,(
% 1.28/0.60    sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_18 | ~spl5_26 | ~spl5_61)),
% 1.28/0.60    inference(forward_demodulation,[],[f540,f279])).
% 1.28/0.60  fof(f279,plain,(
% 1.28/0.60    sK0 = k1_relat_1(sK2) | ~spl5_26),
% 1.28/0.60    inference(avatar_component_clause,[],[f277])).
% 1.28/0.60  fof(f540,plain,(
% 1.28/0.60    k2_funct_1(sK2) = sK3 | k2_relat_1(sK3) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_18 | ~spl5_61)),
% 1.28/0.60    inference(trivial_inequality_removal,[],[f539])).
% 1.28/0.60  fof(f539,plain,(
% 1.28/0.60    k6_partfun1(sK1) != k6_partfun1(sK1) | k2_funct_1(sK2) = sK3 | k2_relat_1(sK3) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_18 | ~spl5_61)),
% 1.28/0.60    inference(forward_demodulation,[],[f538,f190])).
% 1.28/0.60  fof(f190,plain,(
% 1.28/0.60    sK1 = k2_relat_1(sK2) | ~spl5_18),
% 1.28/0.60    inference(avatar_component_clause,[],[f188])).
% 1.28/0.60  fof(f538,plain,(
% 1.28/0.60    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k2_relat_1(sK3) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_61),
% 1.28/0.60    inference(superposition,[],[f83,f533])).
% 1.28/0.60  fof(f533,plain,(
% 1.28/0.60    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~spl5_61),
% 1.28/0.60    inference(avatar_component_clause,[],[f531])).
% 1.28/0.60  fof(f83,plain,(
% 1.28/0.60    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.60    inference(definition_unfolding,[],[f60,f73])).
% 1.28/0.60  fof(f73,plain,(
% 1.28/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.28/0.60    inference(cnf_transformation,[],[f13])).
% 1.28/0.60  fof(f13,axiom,(
% 1.28/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.28/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.28/0.60  fof(f60,plain,(
% 1.28/0.60    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.60    inference(cnf_transformation,[],[f24])).
% 1.28/0.60  fof(f24,plain,(
% 1.28/0.60    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.60    inference(flattening,[],[f23])).
% 1.28/0.60  fof(f23,plain,(
% 1.28/0.60    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.60    inference(ennf_transformation,[],[f6])).
% 1.28/0.60  fof(f6,axiom,(
% 1.28/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.28/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.28/0.60  fof(f534,plain,(
% 1.28/0.60    spl5_61 | ~spl5_29 | ~spl5_60),
% 1.28/0.60    inference(avatar_split_clause,[],[f523,f507,f295,f531])).
% 1.28/0.60  fof(f295,plain,(
% 1.28/0.60    spl5_29 <=> sK2 = k2_funct_1(sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.28/0.60  fof(f507,plain,(
% 1.28/0.60    spl5_60 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 1.28/0.60  fof(f523,plain,(
% 1.28/0.60    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | (~spl5_29 | ~spl5_60)),
% 1.28/0.60    inference(superposition,[],[f509,f297])).
% 1.28/0.60  fof(f297,plain,(
% 1.28/0.60    sK2 = k2_funct_1(sK3) | ~spl5_29),
% 1.28/0.60    inference(avatar_component_clause,[],[f295])).
% 1.28/0.60  fof(f509,plain,(
% 1.28/0.60    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl5_60),
% 1.28/0.60    inference(avatar_component_clause,[],[f507])).
% 1.28/0.60  fof(f522,plain,(
% 1.28/0.60    ~spl5_15 | ~spl5_2 | ~spl5_28 | spl5_31 | ~spl5_60),
% 1.28/0.60    inference(avatar_split_clause,[],[f519,f507,f303,f291,f99,f168])).
% 1.28/0.60  fof(f291,plain,(
% 1.28/0.60    spl5_28 <=> v2_funct_1(sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.28/0.60  fof(f303,plain,(
% 1.28/0.60    spl5_31 <=> sK1 = k1_relat_1(sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.28/0.60  fof(f519,plain,(
% 1.28/0.60    sK1 = k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_60),
% 1.28/0.60    inference(forward_demodulation,[],[f514,f87])).
% 1.28/0.60  fof(f87,plain,(
% 1.28/0.60    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.28/0.60    inference(definition_unfolding,[],[f81,f73])).
% 1.28/0.60  fof(f81,plain,(
% 1.28/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.28/0.60    inference(cnf_transformation,[],[f3])).
% 1.28/0.60  fof(f3,axiom,(
% 1.28/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.28/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.28/0.60  fof(f514,plain,(
% 1.28/0.60    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_60),
% 1.28/0.60    inference(superposition,[],[f62,f509])).
% 1.28/0.60  fof(f62,plain,(
% 1.28/0.60    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.60    inference(cnf_transformation,[],[f26])).
% 1.28/0.60  fof(f26,plain,(
% 1.28/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.60    inference(flattening,[],[f25])).
% 1.28/0.60  fof(f25,plain,(
% 1.28/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.60    inference(ennf_transformation,[],[f5])).
% 1.28/0.60  fof(f5,axiom,(
% 1.28/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 1.28/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.28/0.60  fof(f510,plain,(
% 1.28/0.60    ~spl5_2 | ~spl5_7 | ~spl5_11 | spl5_60 | ~spl5_28 | spl5_4 | ~spl5_38),
% 1.28/0.60    inference(avatar_split_clause,[],[f345,f337,f109,f291,f507,f144,f124,f99])).
% 1.28/0.60  fof(f124,plain,(
% 1.28/0.60    spl5_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.28/0.60  fof(f144,plain,(
% 1.28/0.60    spl5_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.28/0.60  fof(f109,plain,(
% 1.28/0.60    spl5_4 <=> k1_xboole_0 = sK0),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.28/0.60  fof(f337,plain,(
% 1.28/0.60    spl5_38 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.28/0.60  fof(f345,plain,(
% 1.28/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_38),
% 1.28/0.60    inference(trivial_inequality_removal,[],[f343])).
% 1.28/0.60  fof(f343,plain,(
% 1.28/0.60    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_38),
% 1.28/0.60    inference(superposition,[],[f58,f339])).
% 1.28/0.60  fof(f339,plain,(
% 1.28/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl5_38),
% 1.28/0.60    inference(avatar_component_clause,[],[f337])).
% 1.28/0.60  fof(f58,plain,(
% 1.28/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.28/0.60    inference(cnf_transformation,[],[f22])).
% 1.28/0.60  fof(f22,plain,(
% 1.28/0.60    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.28/0.60    inference(flattening,[],[f21])).
% 1.28/0.60  fof(f21,plain,(
% 1.28/0.60    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.28/0.60    inference(ennf_transformation,[],[f16])).
% 1.28/0.60  fof(f16,axiom,(
% 1.28/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.28/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.28/0.60  fof(f415,plain,(
% 1.28/0.60    sK0 != k2_relat_1(sK3) | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.28/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.60  fof(f414,plain,(
% 1.28/0.60    spl5_49),
% 1.28/0.60    inference(avatar_contradiction_clause,[],[f411])).
% 1.28/0.60  fof(f411,plain,(
% 1.28/0.60    $false | spl5_49),
% 1.28/0.60    inference(unit_resulting_resolution,[],[f84,f409])).
% 1.28/0.60  fof(f409,plain,(
% 1.28/0.60    ~v2_funct_1(k6_partfun1(sK0)) | spl5_49),
% 1.28/0.60    inference(avatar_component_clause,[],[f407])).
% 1.28/0.60  fof(f407,plain,(
% 1.28/0.60    spl5_49 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.28/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.28/0.61  fof(f84,plain,(
% 1.28/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.28/0.61    inference(definition_unfolding,[],[f69,f73])).
% 1.28/0.61  fof(f69,plain,(
% 1.28/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.28/0.61    inference(cnf_transformation,[],[f4])).
% 1.28/0.61  fof(f4,axiom,(
% 1.28/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.28/0.61  fof(f410,plain,(
% 1.28/0.61    spl5_28 | spl5_4 | ~spl5_11 | ~spl5_7 | ~spl5_2 | ~spl5_49 | ~spl5_20 | ~spl5_48),
% 1.28/0.61    inference(avatar_split_clause,[],[f403,f400,f204,f407,f99,f124,f144,f109,f291])).
% 1.28/0.61  fof(f204,plain,(
% 1.28/0.61    spl5_20 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.28/0.61  fof(f400,plain,(
% 1.28/0.61    spl5_48 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1))),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.28/0.61  fof(f403,plain,(
% 1.28/0.61    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl5_20 | ~spl5_48)),
% 1.28/0.61    inference(superposition,[],[f401,f206])).
% 1.28/0.61  fof(f206,plain,(
% 1.28/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl5_20),
% 1.28/0.61    inference(avatar_component_clause,[],[f204])).
% 1.28/0.61  fof(f401,plain,(
% 1.28/0.61    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = X0 | v2_funct_1(X1)) ) | ~spl5_48),
% 1.28/0.61    inference(avatar_component_clause,[],[f400])).
% 1.28/0.61  fof(f402,plain,(
% 1.28/0.61    ~spl5_1 | ~spl5_6 | ~spl5_10 | spl5_48 | ~spl5_12),
% 1.28/0.61    inference(avatar_split_clause,[],[f368,f149,f400,f139,f119,f94])).
% 1.28/0.61  fof(f119,plain,(
% 1.28/0.61    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.28/0.61  fof(f139,plain,(
% 1.28/0.61    spl5_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.28/0.61  fof(f149,plain,(
% 1.28/0.61    spl5_12 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.28/0.61  fof(f368,plain,(
% 1.28/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl5_12),
% 1.28/0.61    inference(trivial_inequality_removal,[],[f363])).
% 1.28/0.61  fof(f363,plain,(
% 1.28/0.61    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl5_12),
% 1.28/0.61    inference(superposition,[],[f65,f151])).
% 1.28/0.61  fof(f151,plain,(
% 1.28/0.61    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_12),
% 1.28/0.61    inference(avatar_component_clause,[],[f149])).
% 1.28/0.61  fof(f65,plain,(
% 1.28/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.28/0.61    inference(cnf_transformation,[],[f28])).
% 1.28/0.61  fof(f28,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.28/0.61    inference(flattening,[],[f27])).
% 1.28/0.61  fof(f27,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.28/0.61    inference(ennf_transformation,[],[f15])).
% 1.28/0.61  fof(f15,axiom,(
% 1.28/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.28/0.61  fof(f351,plain,(
% 1.28/0.61    ~spl5_11 | spl5_39 | ~spl5_38),
% 1.28/0.61    inference(avatar_split_clause,[],[f341,f337,f348,f144])).
% 1.28/0.61  fof(f341,plain,(
% 1.28/0.61    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_38),
% 1.28/0.61    inference(superposition,[],[f339,f77])).
% 1.28/0.61  fof(f77,plain,(
% 1.28/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.61    inference(cnf_transformation,[],[f38])).
% 1.28/0.61  fof(f38,plain,(
% 1.28/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.61    inference(ennf_transformation,[],[f8])).
% 1.28/0.61  fof(f8,axiom,(
% 1.28/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.28/0.61  fof(f340,plain,(
% 1.28/0.61    ~spl5_2 | ~spl5_7 | ~spl5_11 | ~spl5_1 | ~spl5_6 | ~spl5_10 | spl5_38 | ~spl5_13),
% 1.28/0.61    inference(avatar_split_clause,[],[f332,f154,f337,f139,f119,f94,f144,f124,f99])).
% 1.28/0.61  fof(f154,plain,(
% 1.28/0.61    spl5_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.28/0.61  fof(f332,plain,(
% 1.28/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_13),
% 1.28/0.61    inference(resolution,[],[f72,f156])).
% 1.28/0.61  fof(f156,plain,(
% 1.28/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl5_13),
% 1.28/0.61    inference(avatar_component_clause,[],[f154])).
% 1.28/0.61  fof(f72,plain,(
% 1.28/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.28/0.61    inference(cnf_transformation,[],[f33])).
% 1.28/0.61  fof(f33,plain,(
% 1.28/0.61    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.28/0.61    inference(flattening,[],[f32])).
% 1.28/0.61  fof(f32,plain,(
% 1.28/0.61    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.28/0.61    inference(ennf_transformation,[],[f14])).
% 1.28/0.61  fof(f14,axiom,(
% 1.28/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.28/0.61  fof(f306,plain,(
% 1.28/0.61    ~spl5_15 | ~spl5_2 | ~spl5_14 | ~spl5_1 | ~spl5_28 | spl5_29 | ~spl5_30 | ~spl5_31 | ~spl5_18 | ~spl5_23),
% 1.28/0.61    inference(avatar_split_clause,[],[f256,f239,f188,f303,f299,f295,f291,f94,f163,f99,f168])).
% 1.28/0.61  fof(f299,plain,(
% 1.28/0.61    spl5_30 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.28/0.61  fof(f239,plain,(
% 1.28/0.61    spl5_23 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.28/0.61  fof(f256,plain,(
% 1.28/0.61    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_18 | ~spl5_23)),
% 1.28/0.61    inference(forward_demodulation,[],[f255,f190])).
% 1.28/0.61  fof(f255,plain,(
% 1.28/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_23),
% 1.28/0.61    inference(superposition,[],[f83,f241])).
% 1.28/0.61  fof(f241,plain,(
% 1.28/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl5_23),
% 1.28/0.61    inference(avatar_component_clause,[],[f239])).
% 1.28/0.61  fof(f280,plain,(
% 1.28/0.61    ~spl5_14 | ~spl5_1 | ~spl5_3 | spl5_26 | ~spl5_25),
% 1.28/0.61    inference(avatar_split_clause,[],[f270,f263,f277,f104,f94,f163])).
% 1.28/0.61  fof(f263,plain,(
% 1.28/0.61    spl5_25 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.28/0.61  fof(f270,plain,(
% 1.28/0.61    sK0 = k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_25),
% 1.28/0.61    inference(forward_demodulation,[],[f267,f87])).
% 1.28/0.61  fof(f267,plain,(
% 1.28/0.61    k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_25),
% 1.28/0.61    inference(superposition,[],[f62,f265])).
% 1.28/0.61  fof(f265,plain,(
% 1.28/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl5_25),
% 1.28/0.61    inference(avatar_component_clause,[],[f263])).
% 1.28/0.61  fof(f266,plain,(
% 1.28/0.61    ~spl5_1 | ~spl5_6 | ~spl5_10 | spl5_25 | ~spl5_3 | spl5_5 | ~spl5_12),
% 1.28/0.61    inference(avatar_split_clause,[],[f246,f149,f114,f104,f263,f139,f119,f94])).
% 1.28/0.61  fof(f114,plain,(
% 1.28/0.61    spl5_5 <=> k1_xboole_0 = sK1),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.28/0.61  fof(f246,plain,(
% 1.28/0.61    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_12),
% 1.28/0.61    inference(trivial_inequality_removal,[],[f243])).
% 1.28/0.61  fof(f243,plain,(
% 1.28/0.61    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_12),
% 1.28/0.61    inference(superposition,[],[f58,f151])).
% 1.28/0.61  fof(f252,plain,(
% 1.28/0.61    ~spl5_1 | ~spl5_10 | ~spl5_2 | ~spl5_11 | spl5_23 | ~spl5_20),
% 1.28/0.61    inference(avatar_split_clause,[],[f228,f204,f239,f144,f99,f139,f94])).
% 1.28/0.61  fof(f228,plain,(
% 1.28/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl5_20),
% 1.28/0.61    inference(superposition,[],[f206,f76])).
% 1.28/0.61  fof(f76,plain,(
% 1.28/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.28/0.61    inference(cnf_transformation,[],[f37])).
% 1.28/0.61  fof(f37,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.28/0.61    inference(flattening,[],[f36])).
% 1.28/0.61  fof(f36,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.28/0.61    inference(ennf_transformation,[],[f12])).
% 1.28/0.61  fof(f12,axiom,(
% 1.28/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.28/0.61  fof(f227,plain,(
% 1.28/0.61    ~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_11 | spl5_19),
% 1.28/0.61    inference(avatar_contradiction_clause,[],[f218])).
% 1.28/0.61  fof(f218,plain,(
% 1.28/0.61    $false | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_11 | spl5_19)),
% 1.28/0.61    inference(unit_resulting_resolution,[],[f96,f101,f141,f146,f202,f75])).
% 1.28/0.61  fof(f75,plain,(
% 1.28/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.28/0.61    inference(cnf_transformation,[],[f35])).
% 1.28/0.61  fof(f35,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.28/0.61    inference(flattening,[],[f34])).
% 1.28/0.61  fof(f34,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.28/0.61    inference(ennf_transformation,[],[f11])).
% 1.28/0.61  fof(f11,axiom,(
% 1.28/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.28/0.61  fof(f202,plain,(
% 1.28/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_19),
% 1.28/0.61    inference(avatar_component_clause,[],[f200])).
% 1.28/0.61  fof(f200,plain,(
% 1.28/0.61    spl5_19 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.28/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.28/0.61  fof(f146,plain,(
% 1.28/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_11),
% 1.28/0.61    inference(avatar_component_clause,[],[f144])).
% 1.28/0.61  fof(f141,plain,(
% 1.28/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_10),
% 1.28/0.61    inference(avatar_component_clause,[],[f139])).
% 1.28/0.61  fof(f101,plain,(
% 1.28/0.61    v1_funct_1(sK3) | ~spl5_2),
% 1.28/0.61    inference(avatar_component_clause,[],[f99])).
% 1.28/0.61  fof(f96,plain,(
% 1.28/0.61    v1_funct_1(sK2) | ~spl5_1),
% 1.28/0.61    inference(avatar_component_clause,[],[f94])).
% 1.28/0.61  fof(f207,plain,(
% 1.28/0.61    ~spl5_19 | spl5_20 | ~spl5_13),
% 1.28/0.61    inference(avatar_split_clause,[],[f197,f154,f204,f200])).
% 1.28/0.61  fof(f197,plain,(
% 1.28/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_13),
% 1.28/0.61    inference(resolution,[],[f194,f156])).
% 1.28/0.61  fof(f194,plain,(
% 1.28/0.61    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.28/0.61    inference(resolution,[],[f70,f86])).
% 1.28/0.61  fof(f86,plain,(
% 1.28/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.28/0.61    inference(definition_unfolding,[],[f79,f73])).
% 1.28/0.61  fof(f79,plain,(
% 1.28/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.28/0.61    inference(cnf_transformation,[],[f10])).
% 1.28/0.61  fof(f10,axiom,(
% 1.28/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.28/0.61  fof(f70,plain,(
% 1.28/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.61    inference(cnf_transformation,[],[f43])).
% 1.28/0.61  fof(f43,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.61    inference(nnf_transformation,[],[f31])).
% 1.28/0.61  fof(f31,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.61    inference(flattening,[],[f30])).
% 1.28/0.61  fof(f30,plain,(
% 1.28/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.28/0.61    inference(ennf_transformation,[],[f9])).
% 1.28/0.61  fof(f9,axiom,(
% 1.28/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.28/0.61  fof(f191,plain,(
% 1.28/0.61    ~spl5_10 | spl5_18 | ~spl5_12),
% 1.28/0.61    inference(avatar_split_clause,[],[f185,f149,f188,f139])).
% 1.28/0.61  fof(f185,plain,(
% 1.28/0.61    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_12),
% 1.28/0.61    inference(superposition,[],[f77,f151])).
% 1.28/0.61  fof(f171,plain,(
% 1.28/0.61    spl5_15 | ~spl5_11),
% 1.28/0.61    inference(avatar_split_clause,[],[f160,f144,f168])).
% 1.28/0.61  fof(f160,plain,(
% 1.28/0.61    v1_relat_1(sK3) | ~spl5_11),
% 1.28/0.61    inference(resolution,[],[f78,f146])).
% 1.28/0.61  fof(f78,plain,(
% 1.28/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.28/0.61    inference(cnf_transformation,[],[f39])).
% 1.28/0.61  fof(f39,plain,(
% 1.28/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.61    inference(ennf_transformation,[],[f7])).
% 1.28/0.61  fof(f7,axiom,(
% 1.28/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.28/0.61  fof(f166,plain,(
% 1.28/0.61    spl5_14 | ~spl5_10),
% 1.28/0.61    inference(avatar_split_clause,[],[f159,f139,f163])).
% 1.28/0.61  fof(f159,plain,(
% 1.28/0.61    v1_relat_1(sK2) | ~spl5_10),
% 1.28/0.61    inference(resolution,[],[f78,f141])).
% 1.28/0.61  fof(f157,plain,(
% 1.28/0.61    spl5_13),
% 1.28/0.61    inference(avatar_split_clause,[],[f53,f154])).
% 1.28/0.61  fof(f53,plain,(
% 1.28/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f42,plain,(
% 1.28/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.28/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).
% 1.28/0.61  fof(f40,plain,(
% 1.28/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.28/0.61    introduced(choice_axiom,[])).
% 1.28/0.61  fof(f41,plain,(
% 1.28/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.28/0.61    introduced(choice_axiom,[])).
% 1.28/0.61  fof(f20,plain,(
% 1.28/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.28/0.61    inference(flattening,[],[f19])).
% 1.28/0.61  fof(f19,plain,(
% 1.28/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.28/0.61    inference(ennf_transformation,[],[f18])).
% 1.28/0.61  fof(f18,negated_conjecture,(
% 1.28/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.28/0.61    inference(negated_conjecture,[],[f17])).
% 1.28/0.61  fof(f17,conjecture,(
% 1.28/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.28/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.28/0.61  fof(f152,plain,(
% 1.28/0.61    spl5_12),
% 1.28/0.61    inference(avatar_split_clause,[],[f52,f149])).
% 1.28/0.61  fof(f52,plain,(
% 1.28/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f147,plain,(
% 1.28/0.61    spl5_11),
% 1.28/0.61    inference(avatar_split_clause,[],[f51,f144])).
% 1.28/0.61  fof(f51,plain,(
% 1.28/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f142,plain,(
% 1.28/0.61    spl5_10),
% 1.28/0.61    inference(avatar_split_clause,[],[f48,f139])).
% 1.28/0.61  fof(f48,plain,(
% 1.28/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f132,plain,(
% 1.28/0.61    ~spl5_8),
% 1.28/0.61    inference(avatar_split_clause,[],[f57,f129])).
% 1.28/0.61  fof(f57,plain,(
% 1.28/0.61    k2_funct_1(sK2) != sK3),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f127,plain,(
% 1.28/0.61    spl5_7),
% 1.28/0.61    inference(avatar_split_clause,[],[f50,f124])).
% 1.28/0.61  fof(f50,plain,(
% 1.28/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f122,plain,(
% 1.28/0.61    spl5_6),
% 1.28/0.61    inference(avatar_split_clause,[],[f47,f119])).
% 1.28/0.61  fof(f47,plain,(
% 1.28/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f117,plain,(
% 1.28/0.61    ~spl5_5),
% 1.28/0.61    inference(avatar_split_clause,[],[f56,f114])).
% 1.28/0.61  fof(f56,plain,(
% 1.28/0.61    k1_xboole_0 != sK1),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f112,plain,(
% 1.28/0.61    ~spl5_4),
% 1.28/0.61    inference(avatar_split_clause,[],[f55,f109])).
% 1.28/0.61  fof(f55,plain,(
% 1.28/0.61    k1_xboole_0 != sK0),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f107,plain,(
% 1.28/0.61    spl5_3),
% 1.28/0.61    inference(avatar_split_clause,[],[f54,f104])).
% 1.28/0.61  fof(f54,plain,(
% 1.28/0.61    v2_funct_1(sK2)),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f102,plain,(
% 1.28/0.61    spl5_2),
% 1.28/0.61    inference(avatar_split_clause,[],[f49,f99])).
% 1.28/0.61  fof(f49,plain,(
% 1.28/0.61    v1_funct_1(sK3)),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  fof(f97,plain,(
% 1.28/0.61    spl5_1),
% 1.28/0.61    inference(avatar_split_clause,[],[f46,f94])).
% 1.28/0.61  fof(f46,plain,(
% 1.28/0.61    v1_funct_1(sK2)),
% 1.28/0.61    inference(cnf_transformation,[],[f42])).
% 1.28/0.61  % SZS output end Proof for theBenchmark
% 1.28/0.61  % (17439)------------------------------
% 1.28/0.61  % (17439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.61  % (17439)Termination reason: Refutation
% 1.28/0.61  
% 1.28/0.61  % (17439)Memory used [KB]: 11385
% 1.28/0.61  % (17439)Time elapsed: 0.180 s
% 1.28/0.61  % (17439)------------------------------
% 1.28/0.61  % (17439)------------------------------
% 1.28/0.61  % (17415)Success in time 0.239 s
%------------------------------------------------------------------------------
