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
% DateTime   : Thu Dec  3 13:02:42 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 318 expanded)
%              Number of leaves         :   39 ( 120 expanded)
%              Depth                    :    8
%              Number of atoms          :  629 (1603 expanded)
%              Number of equality atoms :  140 ( 448 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f791,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f127,f146,f178,f180,f182,f228,f235,f269,f273,f298,f361,f427,f434,f446,f476,f503,f529,f538,f567,f678,f686,f719,f782])).

fof(f782,plain,(
    ~ spl4_73 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f57,f718])).

fof(f718,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl4_73
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f57,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f719,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_7
    | spl4_73
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f708,f246,f716,f164,f254,f250])).

fof(f250,plain,
    ( spl4_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f254,plain,
    ( spl4_18
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f164,plain,
    ( spl4_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f246,plain,
    ( spl4_16
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f708,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(superposition,[],[f72,f248])).

fof(f248,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f246])).

fof(f72,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f686,plain,(
    spl4_71 ),
    inference(avatar_contradiction_clause,[],[f683])).

fof(f683,plain,
    ( $false
    | spl4_71 ),
    inference(unit_resulting_resolution,[],[f93,f677])).

fof(f677,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl4_71
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f64,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f678,plain,
    ( ~ spl4_36
    | ~ spl4_6
    | ~ spl4_7
    | spl4_42
    | spl4_18
    | ~ spl4_71
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f671,f501,f143,f675,f254,f473,f164,f160,f424])).

fof(f424,plain,
    ( spl4_36
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f160,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f473,plain,
    ( spl4_42
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f143,plain,
    ( spl4_4
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f501,plain,
    ( spl4_46
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f671,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(superposition,[],[f502,f145])).

fof(f145,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f501])).

fof(f567,plain,
    ( spl4_20
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl4_20
    | ~ spl4_38 ),
    inference(trivial_inequality_removal,[],[f565])).

fof(f565,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_20
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f264,f444])).

fof(f444,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl4_38
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f264,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl4_20
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f538,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_7
    | spl4_21
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f537,f469,f266,f164,f254,f250])).

fof(f266,plain,
    ( spl4_21
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f469,plain,
    ( spl4_41
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f537,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f533,f96])).

fof(f96,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f533,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_41 ),
    inference(superposition,[],[f75,f471])).

fof(f471,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f469])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f529,plain,(
    ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f55,f475])).

fof(f475,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f473])).

fof(f55,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f503,plain,
    ( ~ spl4_5
    | spl4_46
    | ~ spl4_1
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f499,f291,f116,f501,f156])).

fof(f156,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f116,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f291,plain,
    ( spl4_25
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f499,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f494])).

fof(f494,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f86,f52])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f476,plain,
    ( spl4_41
    | spl4_42
    | ~ spl4_18
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_36
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f439,f420,f424,f160,f164,f254,f473,f469])).

fof(f420,plain,
    ( spl4_35
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f439,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f437])).

fof(f437,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_35 ),
    inference(superposition,[],[f80,f422])).

fof(f422,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f420])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

% (32469)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f18,axiom,(
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

fof(f446,plain,
    ( ~ spl4_6
    | spl4_38
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f438,f420,f442,f160])).

fof(f438,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_35 ),
    inference(superposition,[],[f79,f422])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f434,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl4_36 ),
    inference(subsumption_resolution,[],[f50,f426])).

fof(f426,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f424])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f427,plain,
    ( spl4_35
    | ~ spl4_7
    | ~ spl4_1
    | ~ spl4_25
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f415,f424,f160,f156,f291,f116,f164,f420])).

fof(f415,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f361,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f103,f260])).

fof(f260,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl4_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f103,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f298,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl4_25 ),
    inference(subsumption_resolution,[],[f59,f293])).

fof(f293,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f291])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f273,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f102,f252])).

fof(f252,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f250])).

fof(f102,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f269,plain,
    ( spl4_16
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_5
    | ~ spl4_19
    | ~ spl4_7
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f244,f189,f120,f266,f262,f164,f258,f156,f254,f250,f246])).

fof(f120,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f189,plain,
    ( spl4_10
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f244,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f243,f122])).

fof(f122,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f243,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_10 ),
    inference(superposition,[],[f97,f191])).

fof(f191,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f189])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f77,f61])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f235,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_1
    | spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f232,f143,f189,f116,f164,f160,f156])).

fof(f232,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f89,f145])).

fof(f89,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f228,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f58,f49,f51,f60,f141,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f141,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_3
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f182,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f49,f166])).

fof(f166,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f164])).

fof(f180,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f51,f162])).

fof(f162,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f178,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f58,f158])).

fof(f158,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f146,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f136,f143,f139])).

fof(f136,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f132,f53])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f88,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f127,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f60,f118])).

fof(f118,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f114,f120,f116])).

fof(f114,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f52,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:26:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (32454)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (32455)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (32445)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (32453)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (32462)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (32447)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (32451)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (32461)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (32448)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32449)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32458)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (32466)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (32459)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (32468)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (32460)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (32446)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (32467)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (32470)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (32461)Refutation not found, incomplete strategy% (32461)------------------------------
% 0.22/0.55  % (32461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32450)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (32472)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (32461)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32461)Memory used [KB]: 10746
% 0.22/0.55  % (32461)Time elapsed: 0.128 s
% 0.22/0.55  % (32461)------------------------------
% 0.22/0.55  % (32461)------------------------------
% 0.22/0.56  % (32455)Refutation not found, incomplete strategy% (32455)------------------------------
% 0.22/0.56  % (32455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32455)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32455)Memory used [KB]: 11001
% 0.22/0.56  % (32455)Time elapsed: 0.140 s
% 0.22/0.56  % (32455)------------------------------
% 0.22/0.56  % (32455)------------------------------
% 0.22/0.56  % (32473)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (32456)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (32457)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (32464)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (32474)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (32465)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (32463)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (32471)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (32473)Refutation not found, incomplete strategy% (32473)------------------------------
% 0.22/0.58  % (32473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (32473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (32473)Memory used [KB]: 11001
% 0.22/0.58  % (32473)Time elapsed: 0.144 s
% 0.22/0.58  % (32473)------------------------------
% 0.22/0.58  % (32473)------------------------------
% 1.55/0.58  % (32452)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.59  % (32458)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f791,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(avatar_sat_refutation,[],[f124,f127,f146,f178,f180,f182,f228,f235,f269,f273,f298,f361,f427,f434,f446,f476,f503,f529,f538,f567,f678,f686,f719,f782])).
% 1.55/0.59  fof(f782,plain,(
% 1.55/0.59    ~spl4_73),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f762])).
% 1.55/0.59  fof(f762,plain,(
% 1.55/0.59    $false | ~spl4_73),
% 1.55/0.59    inference(subsumption_resolution,[],[f57,f718])).
% 1.55/0.59  fof(f718,plain,(
% 1.55/0.59    sK3 = k2_funct_1(sK2) | ~spl4_73),
% 1.55/0.59    inference(avatar_component_clause,[],[f716])).
% 1.55/0.59  fof(f716,plain,(
% 1.55/0.59    spl4_73 <=> sK3 = k2_funct_1(sK2)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.55/0.59  fof(f57,plain,(
% 1.55/0.59    sK3 != k2_funct_1(sK2)),
% 1.55/0.59    inference(cnf_transformation,[],[f22])).
% 1.55/0.59  fof(f22,plain,(
% 1.55/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.55/0.59    inference(flattening,[],[f21])).
% 1.55/0.59  fof(f21,plain,(
% 1.55/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.55/0.59    inference(ennf_transformation,[],[f20])).
% 1.55/0.59  fof(f20,negated_conjecture,(
% 1.55/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.55/0.59    inference(negated_conjecture,[],[f19])).
% 1.55/0.59  fof(f19,conjecture,(
% 1.55/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.55/0.59  fof(f719,plain,(
% 1.55/0.59    ~spl4_17 | ~spl4_18 | ~spl4_7 | spl4_73 | ~spl4_16),
% 1.55/0.59    inference(avatar_split_clause,[],[f708,f246,f716,f164,f254,f250])).
% 1.55/0.59  fof(f250,plain,(
% 1.55/0.59    spl4_17 <=> v1_relat_1(sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.55/0.59  fof(f254,plain,(
% 1.55/0.59    spl4_18 <=> v2_funct_1(sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.55/0.59  fof(f164,plain,(
% 1.55/0.59    spl4_7 <=> v1_funct_1(sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.55/0.59  fof(f246,plain,(
% 1.55/0.59    spl4_16 <=> sK2 = k2_funct_1(sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.55/0.59  fof(f708,plain,(
% 1.55/0.59    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_16),
% 1.55/0.59    inference(superposition,[],[f72,f248])).
% 1.55/0.59  fof(f248,plain,(
% 1.55/0.59    sK2 = k2_funct_1(sK3) | ~spl4_16),
% 1.55/0.59    inference(avatar_component_clause,[],[f246])).
% 1.55/0.59  fof(f72,plain,(
% 1.55/0.59    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f28])).
% 1.55/0.59  fof(f28,plain,(
% 1.55/0.59    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.59    inference(flattening,[],[f27])).
% 1.55/0.59  fof(f27,plain,(
% 1.55/0.59    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.55/0.59  fof(f686,plain,(
% 1.55/0.59    spl4_71),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f683])).
% 1.55/0.59  fof(f683,plain,(
% 1.55/0.59    $false | spl4_71),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f93,f677])).
% 1.55/0.59  fof(f677,plain,(
% 1.55/0.59    ~v2_funct_1(k6_partfun1(sK0)) | spl4_71),
% 1.55/0.59    inference(avatar_component_clause,[],[f675])).
% 1.55/0.59  fof(f675,plain,(
% 1.55/0.59    spl4_71 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.55/0.59  fof(f93,plain,(
% 1.55/0.59    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.55/0.59    inference(definition_unfolding,[],[f64,f61])).
% 1.55/0.59  fof(f61,plain,(
% 1.55/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f15])).
% 1.55/0.59  fof(f15,axiom,(
% 1.55/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.55/0.59  fof(f64,plain,(
% 1.55/0.59    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f3])).
% 1.55/0.59  fof(f3,axiom,(
% 1.55/0.59    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.55/0.59  fof(f678,plain,(
% 1.55/0.59    ~spl4_36 | ~spl4_6 | ~spl4_7 | spl4_42 | spl4_18 | ~spl4_71 | ~spl4_4 | ~spl4_46),
% 1.55/0.59    inference(avatar_split_clause,[],[f671,f501,f143,f675,f254,f473,f164,f160,f424])).
% 1.55/0.59  fof(f424,plain,(
% 1.55/0.59    spl4_36 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.55/0.59  fof(f160,plain,(
% 1.55/0.59    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.55/0.59  fof(f473,plain,(
% 1.55/0.59    spl4_42 <=> k1_xboole_0 = sK0),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.55/0.59  fof(f143,plain,(
% 1.55/0.59    spl4_4 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.55/0.59  fof(f501,plain,(
% 1.55/0.59    spl4_46 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.55/0.59  fof(f671,plain,(
% 1.55/0.59    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_4 | ~spl4_46)),
% 1.55/0.59    inference(superposition,[],[f502,f145])).
% 1.55/0.59  fof(f145,plain,(
% 1.55/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_4),
% 1.55/0.59    inference(avatar_component_clause,[],[f143])).
% 1.55/0.59  fof(f502,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_46),
% 1.55/0.59    inference(avatar_component_clause,[],[f501])).
% 1.55/0.59  fof(f567,plain,(
% 1.55/0.59    spl4_20 | ~spl4_38),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f566])).
% 1.55/0.59  fof(f566,plain,(
% 1.55/0.59    $false | (spl4_20 | ~spl4_38)),
% 1.55/0.59    inference(trivial_inequality_removal,[],[f565])).
% 1.55/0.59  fof(f565,plain,(
% 1.55/0.59    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_20 | ~spl4_38)),
% 1.55/0.59    inference(forward_demodulation,[],[f264,f444])).
% 1.55/0.59  fof(f444,plain,(
% 1.55/0.59    sK0 = k2_relat_1(sK3) | ~spl4_38),
% 1.55/0.59    inference(avatar_component_clause,[],[f442])).
% 1.55/0.59  fof(f442,plain,(
% 1.55/0.59    spl4_38 <=> sK0 = k2_relat_1(sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.55/0.59  fof(f264,plain,(
% 1.55/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_20),
% 1.55/0.59    inference(avatar_component_clause,[],[f262])).
% 1.55/0.59  fof(f262,plain,(
% 1.55/0.59    spl4_20 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.55/0.59  fof(f538,plain,(
% 1.55/0.59    ~spl4_17 | ~spl4_18 | ~spl4_7 | spl4_21 | ~spl4_41),
% 1.55/0.59    inference(avatar_split_clause,[],[f537,f469,f266,f164,f254,f250])).
% 1.55/0.59  fof(f266,plain,(
% 1.55/0.59    spl4_21 <=> sK1 = k1_relat_1(sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.55/0.59  fof(f469,plain,(
% 1.55/0.59    spl4_41 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.55/0.59  fof(f537,plain,(
% 1.55/0.59    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_41),
% 1.55/0.59    inference(forward_demodulation,[],[f533,f96])).
% 1.55/0.59  fof(f96,plain,(
% 1.55/0.59    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.55/0.59    inference(definition_unfolding,[],[f65,f61])).
% 1.55/0.59  fof(f65,plain,(
% 1.55/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.55/0.59  fof(f533,plain,(
% 1.55/0.59    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_41),
% 1.55/0.59    inference(superposition,[],[f75,f471])).
% 1.55/0.59  fof(f471,plain,(
% 1.55/0.59    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_41),
% 1.55/0.59    inference(avatar_component_clause,[],[f469])).
% 1.55/0.59  fof(f75,plain,(
% 1.55/0.59    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f32])).
% 1.55/0.59  fof(f32,plain,(
% 1.55/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.59    inference(flattening,[],[f31])).
% 1.55/0.59  fof(f31,plain,(
% 1.55/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f6])).
% 1.55/0.59  fof(f6,axiom,(
% 1.55/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.55/0.59  fof(f529,plain,(
% 1.55/0.59    ~spl4_42),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f514])).
% 1.55/0.59  fof(f514,plain,(
% 1.55/0.59    $false | ~spl4_42),
% 1.55/0.59    inference(subsumption_resolution,[],[f55,f475])).
% 1.55/0.59  fof(f475,plain,(
% 1.55/0.59    k1_xboole_0 = sK0 | ~spl4_42),
% 1.55/0.59    inference(avatar_component_clause,[],[f473])).
% 1.55/0.59  fof(f55,plain,(
% 1.55/0.59    k1_xboole_0 != sK0),
% 1.55/0.59    inference(cnf_transformation,[],[f22])).
% 1.55/0.59  fof(f503,plain,(
% 1.55/0.59    ~spl4_5 | spl4_46 | ~spl4_1 | ~spl4_25),
% 1.55/0.59    inference(avatar_split_clause,[],[f499,f291,f116,f501,f156])).
% 1.55/0.59  fof(f156,plain,(
% 1.55/0.59    spl4_5 <=> v1_funct_1(sK2)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.55/0.59  fof(f116,plain,(
% 1.55/0.59    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.55/0.59  fof(f291,plain,(
% 1.55/0.59    spl4_25 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.55/0.59  fof(f499,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.55/0.59    inference(trivial_inequality_removal,[],[f494])).
% 1.55/0.59  fof(f494,plain,(
% 1.55/0.59    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.55/0.59    inference(superposition,[],[f86,f52])).
% 1.55/0.59  fof(f52,plain,(
% 1.55/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.55/0.59    inference(cnf_transformation,[],[f22])).
% 1.55/0.59  fof(f86,plain,(
% 1.55/0.59    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f42])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.55/0.59    inference(flattening,[],[f41])).
% 1.55/0.59  fof(f41,plain,(
% 1.55/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.55/0.59    inference(ennf_transformation,[],[f17])).
% 1.55/0.59  fof(f17,axiom,(
% 1.55/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.55/0.59  fof(f476,plain,(
% 1.55/0.59    spl4_41 | spl4_42 | ~spl4_18 | ~spl4_7 | ~spl4_6 | ~spl4_36 | ~spl4_35),
% 1.55/0.59    inference(avatar_split_clause,[],[f439,f420,f424,f160,f164,f254,f473,f469])).
% 1.55/0.59  fof(f420,plain,(
% 1.55/0.59    spl4_35 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.55/0.59  fof(f439,plain,(
% 1.55/0.59    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_35),
% 1.55/0.59    inference(trivial_inequality_removal,[],[f437])).
% 1.55/0.59  fof(f437,plain,(
% 1.55/0.59    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_35),
% 1.55/0.59    inference(superposition,[],[f80,f422])).
% 1.55/0.59  fof(f422,plain,(
% 1.55/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_35),
% 1.55/0.59    inference(avatar_component_clause,[],[f420])).
% 1.55/0.59  fof(f80,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f38])).
% 1.55/0.59  fof(f38,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.55/0.59    inference(flattening,[],[f37])).
% 1.55/0.59  fof(f37,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.55/0.59    inference(ennf_transformation,[],[f18])).
% 1.75/0.60  % (32469)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.75/0.61  fof(f18,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.75/0.61  fof(f446,plain,(
% 1.75/0.61    ~spl4_6 | spl4_38 | ~spl4_35),
% 1.75/0.61    inference(avatar_split_clause,[],[f438,f420,f442,f160])).
% 1.75/0.61  fof(f438,plain,(
% 1.75/0.61    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_35),
% 1.75/0.61    inference(superposition,[],[f79,f422])).
% 1.75/0.61  fof(f79,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f36])).
% 1.75/0.61  fof(f36,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(ennf_transformation,[],[f10])).
% 1.75/0.61  fof(f10,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.75/0.61  fof(f434,plain,(
% 1.75/0.61    spl4_36),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f433])).
% 1.75/0.61  fof(f433,plain,(
% 1.75/0.61    $false | spl4_36),
% 1.75/0.61    inference(subsumption_resolution,[],[f50,f426])).
% 1.75/0.61  fof(f426,plain,(
% 1.75/0.61    ~v1_funct_2(sK3,sK1,sK0) | spl4_36),
% 1.75/0.61    inference(avatar_component_clause,[],[f424])).
% 1.75/0.61  fof(f50,plain,(
% 1.75/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f427,plain,(
% 1.75/0.61    spl4_35 | ~spl4_7 | ~spl4_1 | ~spl4_25 | ~spl4_5 | ~spl4_6 | ~spl4_36),
% 1.75/0.61    inference(avatar_split_clause,[],[f415,f424,f160,f156,f291,f116,f164,f420])).
% 1.75/0.61  fof(f415,plain,(
% 1.75/0.61    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.75/0.61    inference(resolution,[],[f82,f53])).
% 1.75/0.61  fof(f53,plain,(
% 1.75/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f82,plain,(
% 1.75/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.75/0.61    inference(cnf_transformation,[],[f40])).
% 1.75/0.61  fof(f40,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.61    inference(flattening,[],[f39])).
% 1.75/0.61  fof(f39,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.61    inference(ennf_transformation,[],[f16])).
% 1.75/0.61  fof(f16,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.75/0.61  fof(f361,plain,(
% 1.75/0.61    spl4_19),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f358])).
% 1.75/0.61  fof(f358,plain,(
% 1.75/0.61    $false | spl4_19),
% 1.75/0.61    inference(subsumption_resolution,[],[f103,f260])).
% 1.75/0.61  fof(f260,plain,(
% 1.75/0.61    ~v1_relat_1(sK2) | spl4_19),
% 1.75/0.61    inference(avatar_component_clause,[],[f258])).
% 1.75/0.61  fof(f258,plain,(
% 1.75/0.61    spl4_19 <=> v1_relat_1(sK2)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.75/0.61  fof(f103,plain,(
% 1.75/0.61    v1_relat_1(sK2)),
% 1.75/0.61    inference(resolution,[],[f78,f60])).
% 1.75/0.61  fof(f60,plain,(
% 1.75/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f78,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f35])).
% 1.75/0.61  fof(f35,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(ennf_transformation,[],[f9])).
% 1.75/0.61  fof(f9,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.75/0.61  fof(f298,plain,(
% 1.75/0.61    spl4_25),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f297])).
% 1.75/0.61  fof(f297,plain,(
% 1.75/0.61    $false | spl4_25),
% 1.75/0.61    inference(subsumption_resolution,[],[f59,f293])).
% 1.75/0.61  fof(f293,plain,(
% 1.75/0.61    ~v1_funct_2(sK2,sK0,sK1) | spl4_25),
% 1.75/0.61    inference(avatar_component_clause,[],[f291])).
% 1.75/0.61  fof(f59,plain,(
% 1.75/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f273,plain,(
% 1.75/0.61    spl4_17),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f270])).
% 1.75/0.61  fof(f270,plain,(
% 1.75/0.61    $false | spl4_17),
% 1.75/0.61    inference(subsumption_resolution,[],[f102,f252])).
% 1.75/0.61  fof(f252,plain,(
% 1.75/0.61    ~v1_relat_1(sK3) | spl4_17),
% 1.75/0.61    inference(avatar_component_clause,[],[f250])).
% 1.75/0.61  fof(f102,plain,(
% 1.75/0.61    v1_relat_1(sK3)),
% 1.75/0.61    inference(resolution,[],[f78,f51])).
% 1.75/0.61  fof(f51,plain,(
% 1.75/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f269,plain,(
% 1.75/0.61    spl4_16 | ~spl4_17 | ~spl4_18 | ~spl4_5 | ~spl4_19 | ~spl4_7 | ~spl4_20 | ~spl4_21 | ~spl4_2 | ~spl4_10),
% 1.75/0.61    inference(avatar_split_clause,[],[f244,f189,f120,f266,f262,f164,f258,f156,f254,f250,f246])).
% 1.75/0.61  fof(f120,plain,(
% 1.75/0.61    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.75/0.61  fof(f189,plain,(
% 1.75/0.61    spl4_10 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.75/0.61  fof(f244,plain,(
% 1.75/0.61    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_2 | ~spl4_10)),
% 1.75/0.61    inference(forward_demodulation,[],[f243,f122])).
% 1.75/0.61  fof(f122,plain,(
% 1.75/0.61    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 1.75/0.61    inference(avatar_component_clause,[],[f120])).
% 1.75/0.61  fof(f243,plain,(
% 1.75/0.61    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_10),
% 1.75/0.61    inference(superposition,[],[f97,f191])).
% 1.75/0.61  fof(f191,plain,(
% 1.75/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_10),
% 1.75/0.61    inference(avatar_component_clause,[],[f189])).
% 1.75/0.61  fof(f97,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.75/0.61    inference(definition_unfolding,[],[f77,f61])).
% 1.75/0.61  fof(f77,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.75/0.61    inference(cnf_transformation,[],[f34])).
% 1.75/0.61  fof(f34,plain,(
% 1.75/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.61    inference(flattening,[],[f33])).
% 1.75/0.61  fof(f33,plain,(
% 1.75/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.61    inference(ennf_transformation,[],[f7])).
% 1.75/0.61  fof(f7,axiom,(
% 1.75/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.75/0.61  fof(f235,plain,(
% 1.75/0.61    ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_1 | spl4_10 | ~spl4_4),
% 1.75/0.61    inference(avatar_split_clause,[],[f232,f143,f189,f116,f164,f160,f156])).
% 1.75/0.61  fof(f232,plain,(
% 1.75/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_4),
% 1.75/0.61    inference(superposition,[],[f89,f145])).
% 1.75/0.61  fof(f89,plain,(
% 1.75/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f46])).
% 1.75/0.61  fof(f46,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.75/0.61    inference(flattening,[],[f45])).
% 1.75/0.61  fof(f45,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.75/0.61    inference(ennf_transformation,[],[f14])).
% 1.75/0.61  fof(f14,axiom,(
% 1.75/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.75/0.61  fof(f228,plain,(
% 1.75/0.61    spl4_3),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f217])).
% 1.75/0.61  fof(f217,plain,(
% 1.75/0.61    $false | spl4_3),
% 1.75/0.61    inference(unit_resulting_resolution,[],[f58,f49,f51,f60,f141,f91])).
% 1.75/0.61  fof(f91,plain,(
% 1.75/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f48])).
% 1.75/0.61  fof(f48,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.75/0.61    inference(flattening,[],[f47])).
% 1.75/0.61  fof(f47,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.75/0.61    inference(ennf_transformation,[],[f13])).
% 1.75/0.61  fof(f13,axiom,(
% 1.75/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.75/0.61  fof(f141,plain,(
% 1.75/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_3),
% 1.75/0.61    inference(avatar_component_clause,[],[f139])).
% 1.75/0.61  fof(f139,plain,(
% 1.75/0.61    spl4_3 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.75/0.61  fof(f49,plain,(
% 1.75/0.61    v1_funct_1(sK3)),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f58,plain,(
% 1.75/0.61    v1_funct_1(sK2)),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f182,plain,(
% 1.75/0.61    spl4_7),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f181])).
% 1.75/0.61  fof(f181,plain,(
% 1.75/0.61    $false | spl4_7),
% 1.75/0.61    inference(subsumption_resolution,[],[f49,f166])).
% 1.75/0.61  fof(f166,plain,(
% 1.75/0.61    ~v1_funct_1(sK3) | spl4_7),
% 1.75/0.61    inference(avatar_component_clause,[],[f164])).
% 1.75/0.61  fof(f180,plain,(
% 1.75/0.61    spl4_6),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f179])).
% 1.75/0.61  fof(f179,plain,(
% 1.75/0.61    $false | spl4_6),
% 1.75/0.61    inference(subsumption_resolution,[],[f51,f162])).
% 1.75/0.61  fof(f162,plain,(
% 1.75/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_6),
% 1.75/0.61    inference(avatar_component_clause,[],[f160])).
% 1.75/0.61  fof(f178,plain,(
% 1.75/0.61    spl4_5),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f177])).
% 1.75/0.61  fof(f177,plain,(
% 1.75/0.61    $false | spl4_5),
% 1.75/0.61    inference(subsumption_resolution,[],[f58,f158])).
% 1.75/0.61  fof(f158,plain,(
% 1.75/0.61    ~v1_funct_1(sK2) | spl4_5),
% 1.75/0.61    inference(avatar_component_clause,[],[f156])).
% 1.75/0.61  fof(f146,plain,(
% 1.75/0.61    ~spl4_3 | spl4_4),
% 1.75/0.61    inference(avatar_split_clause,[],[f136,f143,f139])).
% 1.75/0.61  fof(f136,plain,(
% 1.75/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.75/0.61    inference(resolution,[],[f132,f53])).
% 1.75/0.61  fof(f132,plain,(
% 1.75/0.61    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.75/0.61    inference(resolution,[],[f88,f92])).
% 1.75/0.61  fof(f92,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.75/0.61    inference(definition_unfolding,[],[f62,f61])).
% 1.75/0.61  fof(f62,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f12])).
% 1.75/0.61  fof(f12,axiom,(
% 1.75/0.61    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.75/0.61  fof(f88,plain,(
% 1.75/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f44])).
% 1.75/0.61  fof(f44,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(flattening,[],[f43])).
% 1.75/0.61  fof(f43,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.75/0.61    inference(ennf_transformation,[],[f11])).
% 1.75/0.61  fof(f11,axiom,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.75/0.61  fof(f127,plain,(
% 1.75/0.61    spl4_1),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f126])).
% 1.75/0.61  fof(f126,plain,(
% 1.75/0.61    $false | spl4_1),
% 1.75/0.61    inference(subsumption_resolution,[],[f60,f118])).
% 1.75/0.61  fof(f118,plain,(
% 1.75/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 1.75/0.61    inference(avatar_component_clause,[],[f116])).
% 1.75/0.61  fof(f124,plain,(
% 1.75/0.61    ~spl4_1 | spl4_2),
% 1.75/0.61    inference(avatar_split_clause,[],[f114,f120,f116])).
% 1.75/0.61  fof(f114,plain,(
% 1.75/0.61    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.61    inference(superposition,[],[f52,f79])).
% 1.75/0.61  % SZS output end Proof for theBenchmark
% 1.75/0.61  % (32458)------------------------------
% 1.75/0.61  % (32458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.61  % (32458)Termination reason: Refutation
% 1.75/0.61  
% 1.75/0.61  % (32458)Memory used [KB]: 6780
% 1.75/0.61  % (32458)Time elapsed: 0.140 s
% 1.75/0.61  % (32458)------------------------------
% 1.75/0.61  % (32458)------------------------------
% 1.75/0.61  % (32444)Success in time 0.238 s
%------------------------------------------------------------------------------
