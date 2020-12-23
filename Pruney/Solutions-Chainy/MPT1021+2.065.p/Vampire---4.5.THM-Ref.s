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
% DateTime   : Thu Dec  3 13:06:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 314 expanded)
%              Number of leaves         :   43 ( 148 expanded)
%              Depth                    :    8
%              Number of atoms          :  565 ( 983 expanded)
%              Number of equality atoms :   68 ( 126 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f817,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f143,f148,f162,f166,f172,f177,f186,f193,f229,f256,f266,f271,f287,f305,f351,f393,f514,f524,f579,f587,f592,f682,f727,f813,f816])).

fof(f816,plain,
    ( ~ spl2_40
    | ~ spl2_57
    | spl2_69 ),
    inference(avatar_contradiction_clause,[],[f814])).

fof(f814,plain,
    ( $false
    | ~ spl2_40
    | ~ spl2_57
    | spl2_69 ),
    inference(unit_resulting_resolution,[],[f392,f726,f812,f91])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f812,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl2_69 ),
    inference(avatar_component_clause,[],[f810])).

fof(f810,plain,
    ( spl2_69
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f726,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f724])).

fof(f724,plain,
    ( spl2_57
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f392,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl2_40
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f813,plain,
    ( ~ spl2_69
    | spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f760,f183,f179,f810])).

fof(f179,plain,
    ( spl2_14
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f183,plain,
    ( spl2_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f760,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f180,f185])).

fof(f185,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f180,plain,
    ( sK0 != k1_relset_1(sK0,sK0,sK1)
    | spl2_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f727,plain,
    ( spl2_57
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f688,f183,f114,f724])).

fof(f114,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f688,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f116,f185])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f682,plain,
    ( ~ spl2_8
    | ~ spl2_13
    | ~ spl2_43
    | ~ spl2_53 ),
    inference(avatar_contradiction_clause,[],[f679])).

fof(f679,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_13
    | ~ spl2_43
    | ~ spl2_53 ),
    inference(unit_resulting_resolution,[],[f147,f176,f585,f513])).

fof(f513,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl2_43
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f585,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl2_53
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f176,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_13
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f147,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f592,plain,(
    spl2_53 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | spl2_53 ),
    inference(unit_resulting_resolution,[],[f88,f586,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f586,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl2_53 ),
    inference(avatar_component_clause,[],[f584])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f56,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f587,plain,
    ( ~ spl2_10
    | ~ spl2_12
    | ~ spl2_1
    | ~ spl2_53
    | ~ spl2_16
    | spl2_52 ),
    inference(avatar_split_clause,[],[f581,f576,f190,f584,f99,f169,f155])).

fof(f155,plain,
    ( spl2_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f169,plain,
    ( spl2_12
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f99,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f190,plain,
    ( spl2_16
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f576,plain,
    ( spl2_52
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f581,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_16
    | spl2_52 ),
    inference(forward_demodulation,[],[f580,f192])).

fof(f192,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f580,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_52 ),
    inference(superposition,[],[f578,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f578,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_52 ),
    inference(avatar_component_clause,[],[f576])).

fof(f579,plain,
    ( ~ spl2_1
    | ~ spl2_28
    | ~ spl2_24
    | ~ spl2_4
    | ~ spl2_52
    | spl2_44 ),
    inference(avatar_split_clause,[],[f525,f521,f576,f114,f263,f284,f99])).

fof(f284,plain,
    ( spl2_28
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f263,plain,
    ( spl2_24
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f521,plain,
    ( spl2_44
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f525,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl2_44 ),
    inference(superposition,[],[f523,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f523,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_44 ),
    inference(avatar_component_clause,[],[f521])).

fof(f524,plain,
    ( ~ spl2_44
    | spl2_7
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f515,f253,f140,f521])).

fof(f140,plain,
    ( spl2_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f253,plain,
    ( spl2_23
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f515,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_7
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f142,f255])).

fof(f255,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f253])).

fof(f142,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f514,plain,
    ( ~ spl2_10
    | spl2_43
    | spl2_38 ),
    inference(avatar_split_clause,[],[f352,f348,f512,f155])).

fof(f348,plain,
    ( spl2_38
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v2_funct_2(sK1,X0) )
    | spl2_38 ),
    inference(superposition,[],[f350,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f350,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | spl2_38 ),
    inference(avatar_component_clause,[],[f348])).

fof(f393,plain,
    ( spl2_40
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f358,f183,f104,f390])).

fof(f104,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f358,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f106,f185])).

fof(f106,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f351,plain,
    ( ~ spl2_10
    | ~ spl2_12
    | ~ spl2_1
    | ~ spl2_38
    | spl2_29 ),
    inference(avatar_split_clause,[],[f326,f302,f348,f99,f169,f155])).

fof(f302,plain,
    ( spl2_29
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f326,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_29 ),
    inference(superposition,[],[f304,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f304,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f302])).

fof(f305,plain,
    ( ~ spl2_24
    | ~ spl2_4
    | ~ spl2_1
    | ~ spl2_28
    | ~ spl2_29
    | spl2_25 ),
    inference(avatar_split_clause,[],[f272,f268,f302,f284,f99,f114,f263])).

fof(f268,plain,
    ( spl2_25
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f272,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl2_25 ),
    inference(superposition,[],[f270,f86])).

fof(f270,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f268])).

fof(f287,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_2
    | spl2_28
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f261,f253,f284,f104,f109,f114,f99])).

fof(f109,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f261,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl2_23 ),
    inference(superposition,[],[f71,f255])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f271,plain,
    ( ~ spl2_25
    | spl2_6
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f258,f253,f136,f268])).

fof(f136,plain,
    ( spl2_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f258,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_6
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f138,f255])).

fof(f138,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f266,plain,
    ( spl2_24
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f257,f253,f226,f263])).

fof(f226,plain,
    ( spl2_18
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f257,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_18
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f228,f255])).

fof(f228,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f226])).

fof(f256,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f119,f114,f104,f109,f99,f253])).

fof(f119,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f229,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f118,f114,f104,f109,f99,f226])).

fof(f118,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f193,plain,
    ( ~ spl2_4
    | spl2_16
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f187,f179,f190,f114])).

fof(f187,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_14 ),
    inference(superposition,[],[f181,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f181,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f186,plain,
    ( ~ spl2_2
    | spl2_14
    | spl2_15
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f123,f114,f183,f179,f104])).

fof(f123,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f177,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f125,f114,f99,f109,f174])).

fof(f125,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f172,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f124,f114,f99,f109,f169])).

fof(f124,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f166,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f64,f161])).

fof(f161,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl2_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f162,plain,
    ( spl2_10
    | ~ spl2_11
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f129,f114,f159,f155])).

fof(f129,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f148,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f121,f114,f145])).

fof(f121,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f143,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f87,f140,f136])).

fof(f87,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f47,f56,f56])).

fof(f47,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f117,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f51,f114])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f50,f109])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f49,f104])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:14:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (26552)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (26570)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (26561)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (26581)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (26554)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (26578)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (26558)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26567)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (26556)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (26574)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (26557)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (26577)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (26560)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (26555)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (26562)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (26580)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (26569)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (26573)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (26563)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (26571)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (26582)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (26564)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (26566)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (26576)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (26579)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (26553)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (26575)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (26559)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (26565)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.58  % (26581)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f817,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f143,f148,f162,f166,f172,f177,f186,f193,f229,f256,f266,f271,f287,f305,f351,f393,f514,f524,f579,f587,f592,f682,f727,f813,f816])).
% 0.22/0.58  fof(f816,plain,(
% 0.22/0.58    ~spl2_40 | ~spl2_57 | spl2_69),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f814])).
% 0.22/0.58  fof(f814,plain,(
% 0.22/0.58    $false | (~spl2_40 | ~spl2_57 | spl2_69)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f392,f726,f812,f91])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f78])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.58  fof(f812,plain,(
% 0.22/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | spl2_69),
% 0.22/0.58    inference(avatar_component_clause,[],[f810])).
% 0.22/0.58  fof(f810,plain,(
% 0.22/0.58    spl2_69 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.22/0.58  fof(f726,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_57),
% 0.22/0.58    inference(avatar_component_clause,[],[f724])).
% 0.22/0.58  fof(f724,plain,(
% 0.22/0.58    spl2_57 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.22/0.58  fof(f392,plain,(
% 0.22/0.58    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_40),
% 0.22/0.58    inference(avatar_component_clause,[],[f390])).
% 0.22/0.58  fof(f390,plain,(
% 0.22/0.58    spl2_40 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.58  fof(f813,plain,(
% 0.22/0.58    ~spl2_69 | spl2_14 | ~spl2_15),
% 0.22/0.58    inference(avatar_split_clause,[],[f760,f183,f179,f810])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    spl2_14 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.58  fof(f183,plain,(
% 0.22/0.58    spl2_15 <=> k1_xboole_0 = sK0),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.58  fof(f760,plain,(
% 0.22/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (spl2_14 | ~spl2_15)),
% 0.22/0.58    inference(forward_demodulation,[],[f180,f185])).
% 0.22/0.58  fof(f185,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | ~spl2_15),
% 0.22/0.58    inference(avatar_component_clause,[],[f183])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    sK0 != k1_relset_1(sK0,sK0,sK1) | spl2_14),
% 0.22/0.58    inference(avatar_component_clause,[],[f179])).
% 0.22/0.58  fof(f727,plain,(
% 0.22/0.58    spl2_57 | ~spl2_4 | ~spl2_15),
% 0.22/0.58    inference(avatar_split_clause,[],[f688,f183,f114,f724])).
% 0.22/0.58  fof(f114,plain,(
% 0.22/0.58    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.58  fof(f688,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_4 | ~spl2_15)),
% 0.22/0.58    inference(backward_demodulation,[],[f116,f185])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f114])).
% 0.22/0.58  fof(f682,plain,(
% 0.22/0.58    ~spl2_8 | ~spl2_13 | ~spl2_43 | ~spl2_53),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f679])).
% 0.22/0.58  fof(f679,plain,(
% 0.22/0.58    $false | (~spl2_8 | ~spl2_13 | ~spl2_43 | ~spl2_53)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f147,f176,f585,f513])).
% 0.22/0.58  fof(f513,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) ) | ~spl2_43),
% 0.22/0.58    inference(avatar_component_clause,[],[f512])).
% 0.22/0.58  fof(f512,plain,(
% 0.22/0.58    spl2_43 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.22/0.58  fof(f585,plain,(
% 0.22/0.58    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl2_53),
% 0.22/0.58    inference(avatar_component_clause,[],[f584])).
% 0.22/0.58  fof(f584,plain,(
% 0.22/0.58    spl2_53 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.22/0.58  fof(f176,plain,(
% 0.22/0.58    v2_funct_2(sK1,sK0) | ~spl2_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f174])).
% 0.22/0.58  fof(f174,plain,(
% 0.22/0.58    spl2_13 <=> v2_funct_2(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    v5_relat_1(sK1,sK0) | ~spl2_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f145])).
% 0.22/0.58  fof(f145,plain,(
% 0.22/0.58    spl2_8 <=> v5_relat_1(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.58  fof(f592,plain,(
% 0.22/0.58    spl2_53),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f589])).
% 0.22/0.58  fof(f589,plain,(
% 0.22/0.58    $false | spl2_53),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f88,f586,f97])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.58    inference(equality_resolution,[],[f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.58  fof(f586,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl2_53),
% 0.22/0.58    inference(avatar_component_clause,[],[f584])).
% 0.22/0.58  fof(f88,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f58,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,axiom,(
% 0.22/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.58  fof(f587,plain,(
% 0.22/0.58    ~spl2_10 | ~spl2_12 | ~spl2_1 | ~spl2_53 | ~spl2_16 | spl2_52),
% 0.22/0.58    inference(avatar_split_clause,[],[f581,f576,f190,f584,f99,f169,f155])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    spl2_10 <=> v1_relat_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.58  fof(f169,plain,(
% 0.22/0.58    spl2_12 <=> v2_funct_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    spl2_1 <=> v1_funct_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    spl2_16 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.58  fof(f576,plain,(
% 0.22/0.58    spl2_52 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.22/0.58  fof(f581,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_16 | spl2_52)),
% 0.22/0.58    inference(forward_demodulation,[],[f580,f192])).
% 0.22/0.58  fof(f192,plain,(
% 0.22/0.58    sK0 = k1_relat_1(sK1) | ~spl2_16),
% 0.22/0.58    inference(avatar_component_clause,[],[f190])).
% 0.22/0.58  fof(f580,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_52),
% 0.22/0.58    inference(superposition,[],[f578,f62])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(flattening,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.58  fof(f578,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_52),
% 0.22/0.58    inference(avatar_component_clause,[],[f576])).
% 0.22/0.58  fof(f579,plain,(
% 0.22/0.58    ~spl2_1 | ~spl2_28 | ~spl2_24 | ~spl2_4 | ~spl2_52 | spl2_44),
% 0.22/0.58    inference(avatar_split_clause,[],[f525,f521,f576,f114,f263,f284,f99])).
% 0.22/0.58  fof(f284,plain,(
% 0.22/0.58    spl2_28 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.58  fof(f263,plain,(
% 0.22/0.58    spl2_24 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.58  fof(f521,plain,(
% 0.22/0.58    spl2_44 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.22/0.58  fof(f525,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl2_44),
% 0.22/0.58    inference(superposition,[],[f523,f86])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.58    inference(flattening,[],[f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.58    inference(ennf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.58  fof(f523,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_44),
% 0.22/0.58    inference(avatar_component_clause,[],[f521])).
% 0.22/0.58  fof(f524,plain,(
% 0.22/0.58    ~spl2_44 | spl2_7 | ~spl2_23),
% 0.22/0.58    inference(avatar_split_clause,[],[f515,f253,f140,f521])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    spl2_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.58  fof(f253,plain,(
% 0.22/0.58    spl2_23 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.58  fof(f515,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (spl2_7 | ~spl2_23)),
% 0.22/0.58    inference(forward_demodulation,[],[f142,f255])).
% 0.22/0.58  fof(f255,plain,(
% 0.22/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_23),
% 0.22/0.58    inference(avatar_component_clause,[],[f253])).
% 0.22/0.58  fof(f142,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f140])).
% 0.22/0.58  fof(f514,plain,(
% 0.22/0.58    ~spl2_10 | spl2_43 | spl2_38),
% 0.22/0.58    inference(avatar_split_clause,[],[f352,f348,f512,f155])).
% 0.22/0.58  fof(f348,plain,(
% 0.22/0.58    spl2_38 <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.22/0.58  fof(f352,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X0)) ) | spl2_38),
% 0.22/0.58    inference(superposition,[],[f350,f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.58  fof(f350,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | spl2_38),
% 0.22/0.58    inference(avatar_component_clause,[],[f348])).
% 0.22/0.58  fof(f393,plain,(
% 0.22/0.58    spl2_40 | ~spl2_2 | ~spl2_15),
% 0.22/0.58    inference(avatar_split_clause,[],[f358,f183,f104,f390])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.58  fof(f358,plain,(
% 0.22/0.58    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_2 | ~spl2_15)),
% 0.22/0.58    inference(backward_demodulation,[],[f106,f185])).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f104])).
% 0.22/0.58  fof(f351,plain,(
% 0.22/0.58    ~spl2_10 | ~spl2_12 | ~spl2_1 | ~spl2_38 | spl2_29),
% 0.22/0.58    inference(avatar_split_clause,[],[f326,f302,f348,f99,f169,f155])).
% 0.22/0.58  fof(f302,plain,(
% 0.22/0.58    spl2_29 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.58  fof(f326,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_29),
% 0.22/0.58    inference(superposition,[],[f304,f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f304,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_29),
% 0.22/0.58    inference(avatar_component_clause,[],[f302])).
% 0.22/0.58  fof(f305,plain,(
% 0.22/0.58    ~spl2_24 | ~spl2_4 | ~spl2_1 | ~spl2_28 | ~spl2_29 | spl2_25),
% 0.22/0.58    inference(avatar_split_clause,[],[f272,f268,f302,f284,f99,f114,f263])).
% 0.22/0.58  fof(f268,plain,(
% 0.22/0.58    spl2_25 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.58  fof(f272,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl2_25),
% 0.22/0.58    inference(superposition,[],[f270,f86])).
% 0.22/0.58  fof(f270,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_25),
% 0.22/0.58    inference(avatar_component_clause,[],[f268])).
% 0.22/0.58  fof(f287,plain,(
% 0.22/0.58    ~spl2_1 | ~spl2_4 | ~spl2_3 | ~spl2_2 | spl2_28 | ~spl2_23),
% 0.22/0.58    inference(avatar_split_clause,[],[f261,f253,f284,f104,f109,f114,f99])).
% 0.22/0.58  fof(f109,plain,(
% 0.22/0.58    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.58  fof(f261,plain,(
% 0.22/0.58    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl2_23),
% 0.22/0.58    inference(superposition,[],[f71,f255])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.58    inference(flattening,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.58  fof(f271,plain,(
% 0.22/0.58    ~spl2_25 | spl2_6 | ~spl2_23),
% 0.22/0.58    inference(avatar_split_clause,[],[f258,f253,f136,f268])).
% 0.22/0.58  fof(f136,plain,(
% 0.22/0.58    spl2_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.58  fof(f258,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (spl2_6 | ~spl2_23)),
% 0.22/0.58    inference(backward_demodulation,[],[f138,f255])).
% 0.22/0.58  fof(f138,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f136])).
% 0.22/0.58  fof(f266,plain,(
% 0.22/0.58    spl2_24 | ~spl2_18 | ~spl2_23),
% 0.22/0.58    inference(avatar_split_clause,[],[f257,f253,f226,f263])).
% 0.22/0.58  fof(f226,plain,(
% 0.22/0.58    spl2_18 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.58  fof(f257,plain,(
% 0.22/0.58    v1_funct_1(k2_funct_1(sK1)) | (~spl2_18 | ~spl2_23)),
% 0.22/0.58    inference(backward_demodulation,[],[f228,f255])).
% 0.22/0.58  fof(f228,plain,(
% 0.22/0.58    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl2_18),
% 0.22/0.58    inference(avatar_component_clause,[],[f226])).
% 0.22/0.58  fof(f256,plain,(
% 0.22/0.58    spl2_23 | ~spl2_1 | ~spl2_3 | ~spl2_2 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f119,f114,f104,f109,f99,f253])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.58    inference(flattening,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.58  fof(f229,plain,(
% 0.22/0.58    spl2_18 | ~spl2_1 | ~spl2_3 | ~spl2_2 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f118,f114,f104,f109,f99,f226])).
% 0.22/0.58  fof(f118,plain,(
% 0.22/0.58    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f68])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f193,plain,(
% 0.22/0.58    ~spl2_4 | spl2_16 | ~spl2_14),
% 0.22/0.58    inference(avatar_split_clause,[],[f187,f179,f190,f114])).
% 0.22/0.58  fof(f187,plain,(
% 0.22/0.58    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_14),
% 0.22/0.58    inference(superposition,[],[f181,f72])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_14),
% 0.22/0.58    inference(avatar_component_clause,[],[f179])).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    ~spl2_2 | spl2_14 | spl2_15 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f123,f114,f183,f179,f104])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    spl2_13 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f125,f114,f99,f109,f174])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_2(sK1,sK0) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f82])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.58  fof(f172,plain,(
% 0.22/0.58    spl2_12 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f124,f114,f99,f109,f169])).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f81])).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f40])).
% 0.22/0.58  fof(f166,plain,(
% 0.22/0.58    spl2_11),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f163])).
% 0.22/0.58  fof(f163,plain,(
% 0.22/0.58    $false | spl2_11),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f64,f161])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl2_11),
% 0.22/0.58    inference(avatar_component_clause,[],[f159])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    spl2_11 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    spl2_10 | ~spl2_11 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f129,f114,f159,f155])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    spl2_8 | ~spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f121,f114,f145])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    v5_relat_1(sK1,sK0) | ~spl2_4),
% 0.22/0.58    inference(resolution,[],[f116,f74])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.58  fof(f143,plain,(
% 0.22/0.58    ~spl2_6 | ~spl2_7),
% 0.22/0.58    inference(avatar_split_clause,[],[f87,f140,f136])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.22/0.58    inference(definition_unfolding,[],[f47,f56,f56])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.58    inference(flattening,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.58    inference(negated_conjecture,[],[f20])).
% 0.22/0.58  fof(f20,conjecture,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    spl2_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f51,f114])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f112,plain,(
% 0.22/0.58    spl2_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f50,f109])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    spl2_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f49,f104])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    spl2_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f48,f99])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    v1_funct_1(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (26581)------------------------------
% 0.22/0.58  % (26581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (26581)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (26581)Memory used [KB]: 11257
% 0.22/0.58  % (26581)Time elapsed: 0.140 s
% 0.22/0.58  % (26581)------------------------------
% 0.22/0.58  % (26581)------------------------------
% 0.22/0.58  % (26551)Success in time 0.21 s
%------------------------------------------------------------------------------
