%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 294 expanded)
%              Number of leaves         :   36 ( 127 expanded)
%              Depth                    :   11
%              Number of atoms          :  529 (1092 expanded)
%              Number of equality atoms :   93 ( 232 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f566,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f130,f135,f144,f151,f187,f195,f204,f303,f328,f365,f384,f396,f410,f417,f423,f466,f473,f483,f501,f538,f539,f554,f563])).

fof(f563,plain,
    ( spl8_28
    | ~ spl8_45
    | ~ spl8_51 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | spl8_28
    | ~ spl8_45
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f561,f472])).

fof(f472,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl8_45
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f561,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl8_28
    | ~ spl8_51 ),
    inference(subsumption_resolution,[],[f559,f327])).

fof(f327,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl8_28
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f559,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl8_51 ),
    inference(trivial_inequality_removal,[],[f556])).

fof(f556,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl8_51 ),
    inference(superposition,[],[f102,f553])).

fof(f553,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl8_51
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f554,plain,
    ( spl8_51
    | ~ spl8_45
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f549,f498,f470,f551])).

fof(f498,plain,
    ( spl8_48
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f549,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl8_45
    | ~ spl8_48 ),
    inference(forward_demodulation,[],[f490,f500])).

fof(f500,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f498])).

fof(f490,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl8_45 ),
    inference(resolution,[],[f472,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f539,plain,
    ( spl8_50
    | ~ spl8_43
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f527,f480,f457,f535])).

fof(f535,plain,
    ( spl8_50
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f457,plain,
    ( spl8_43
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f480,plain,
    ( spl8_47
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f527,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_43
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f513,f459])).

fof(f459,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f457])).

fof(f513,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_47 ),
    inference(resolution,[],[f482,f103])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f482,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f480])).

fof(f538,plain,
    ( ~ spl8_50
    | ~ spl8_6
    | ~ spl8_7
    | spl8_25 ),
    inference(avatar_split_clause,[],[f508,f285,f141,f137,f535])).

fof(f137,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f141,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f285,plain,
    ( spl8_25
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f508,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_6
    | ~ spl8_7
    | spl8_25 ),
    inference(forward_demodulation,[],[f507,f143])).

fof(f143,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f507,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl8_6
    | spl8_25 ),
    inference(forward_demodulation,[],[f286,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f286,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f501,plain,
    ( spl8_48
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f440,f300,f141,f498])).

fof(f300,plain,
    ( spl8_26
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f440,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(backward_demodulation,[],[f302,f143])).

fof(f302,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f300])).

fof(f483,plain,
    ( spl8_47
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f468,f141,f137,f132,f480])).

fof(f132,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f468,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f430,f143])).

fof(f430,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f134,f138])).

fof(f134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f473,plain,
    ( spl8_45
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f467,f201,f141,f470])).

fof(f201,plain,
    ( spl8_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f467,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f202,f143])).

fof(f202,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f201])).

fof(f466,plain,
    ( spl8_43
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f450,f141,f137,f127,f457])).

fof(f127,plain,
    ( spl8_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f450,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f429,f143])).

fof(f429,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f129,f138])).

fof(f129,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f423,plain,
    ( ~ spl8_13
    | spl8_15
    | ~ spl8_39 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl8_13
    | spl8_15
    | ~ spl8_39 ),
    inference(unit_resulting_resolution,[],[f194,f408,f203,f108])).

fof(f108,plain,(
    ! [X2,X3,X1] :
      ( ~ sP6(X3,X2)
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(general_splitting,[],[f88,f107_D])).

fof(f107,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | sP6(X3,X2) ) ),
    inference(cnf_transformation,[],[f107_D])).

fof(f107_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    <=> ~ sP6(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f203,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f201])).

fof(f408,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl8_39
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f194,plain,
    ( sP6(sK3,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl8_13
  <=> sP6(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f417,plain,
    ( ~ spl8_2
    | ~ spl8_8
    | ~ spl8_12
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_12
    | spl8_39 ),
    inference(unit_resulting_resolution,[],[f119,f186,f150,f409,f182])).

fof(f182,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k2_relat_1(X5),X4)
      | ~ v5_relat_1(X5,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f409,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl8_39 ),
    inference(avatar_component_clause,[],[f407])).

fof(f150,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f186,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_12
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f119,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f410,plain,
    ( ~ spl8_39
    | spl8_14
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f401,f394,f197,f407])).

fof(f197,plain,
    ( spl8_14
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f394,plain,
    ( spl8_37
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | v1_funct_2(sK3,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f401,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl8_14
    | ~ spl8_37 ),
    inference(resolution,[],[f395,f199])).

fof(f199,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f395,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f394])).

fof(f396,plain,
    ( spl8_37
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_31
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f392,f382,f357,f137,f132,f127,f394])).

fof(f357,plain,
    ( spl8_31
  <=> k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f382,plain,
    ( spl8_35
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k2_relset_1(X1,X0,sK3),X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | v1_funct_2(sK3,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | v1_funct_2(sK3,sK0,X0) )
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_31
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f391,f359])).

fof(f359,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X0)
        | v1_funct_2(sK3,sK0,X0) )
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f390,f129])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X0)
        | ~ v1_funct_2(sK3,sK0,sK1)
        | v1_funct_2(sK3,sK0,X0) )
    | ~ spl8_5
    | spl8_6
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f389,f139])).

fof(f139,plain,
    ( k1_xboole_0 != sK1
    | spl8_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),X0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_2(sK3,sK0,sK1)
        | v1_funct_2(sK3,sK0,X0) )
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(resolution,[],[f383,f134])).

fof(f383,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k2_relset_1(X1,X0,sK3),X2)
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0)
        | v1_funct_2(sK3,X1,X2) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f382])).

fof(f384,plain,
    ( spl8_35
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f266,f112,f382])).

fof(f112,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f266,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k2_relset_1(X1,X0,sK3),X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | v1_funct_2(sK3,X1,X2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f91,f114])).

fof(f114,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

% (13844)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (13827)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (13846)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (13845)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (13826)Refutation not found, incomplete strategy% (13826)------------------------------
% (13826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13826)Termination reason: Refutation not found, incomplete strategy

% (13826)Memory used [KB]: 10618
% (13826)Time elapsed: 0.114 s
% (13826)------------------------------
% (13826)------------------------------
% (13832)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (13831)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (13843)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f365,plain,
    ( spl8_31
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f342,f132,f357])).

fof(f342,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f134,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f328,plain,
    ( ~ spl8_28
    | ~ spl8_7
    | spl8_14 ),
    inference(avatar_split_clause,[],[f310,f197,f141,f325])).

fof(f310,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl8_7
    | spl8_14 ),
    inference(backward_demodulation,[],[f199,f143])).

fof(f303,plain,
    ( spl8_26
    | ~ spl8_5
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f298,f285,f132,f300])).

fof(f298,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_5
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f209,f287])).

fof(f287,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f209,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f77,f134])).

fof(f204,plain,
    ( ~ spl8_14
    | ~ spl8_15
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f190,f112,f201,f197])).

fof(f190,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f60,f114])).

fof(f60,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f195,plain,
    ( spl8_13
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f188,f132,f192])).

fof(f188,plain,
    ( sP6(sK3,sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f107,f134])).

fof(f187,plain,
    ( spl8_12
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f174,f132,f184])).

fof(f174,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f80,f134])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f151,plain,
    ( spl8_8
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f146,f132,f148])).

fof(f146,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f76,f134])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f144,plain,
    ( ~ spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f59,f141,f137])).

fof(f59,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f57,f132])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f130,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f56,f127])).

fof(f56,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f58,f117])).

fof(f58,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (13835)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (13838)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (13828)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (13826)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (13842)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (13837)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (13850)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (13836)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (13834)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (13848)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (13830)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (13833)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (13851)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (13833)Refutation not found, incomplete strategy% (13833)------------------------------
% 0.20/0.52  % (13833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13833)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13833)Memory used [KB]: 1663
% 0.20/0.52  % (13833)Time elapsed: 0.103 s
% 0.20/0.52  % (13833)------------------------------
% 0.20/0.52  % (13833)------------------------------
% 0.20/0.52  % (13829)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (13828)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f566,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f115,f120,f130,f135,f144,f151,f187,f195,f204,f303,f328,f365,f384,f396,f410,f417,f423,f466,f473,f483,f501,f538,f539,f554,f563])).
% 0.20/0.52  fof(f563,plain,(
% 0.20/0.52    spl8_28 | ~spl8_45 | ~spl8_51),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f562])).
% 0.20/0.52  fof(f562,plain,(
% 0.20/0.52    $false | (spl8_28 | ~spl8_45 | ~spl8_51)),
% 0.20/0.52    inference(subsumption_resolution,[],[f561,f472])).
% 0.20/0.52  fof(f472,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~spl8_45),
% 0.20/0.52    inference(avatar_component_clause,[],[f470])).
% 0.20/0.52  fof(f470,plain,(
% 0.20/0.52    spl8_45 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.20/0.52  fof(f561,plain,(
% 0.20/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (spl8_28 | ~spl8_51)),
% 0.20/0.52    inference(subsumption_resolution,[],[f559,f327])).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl8_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f325])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    spl8_28 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.20/0.52  fof(f559,plain,(
% 0.20/0.52    v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~spl8_51),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f556])).
% 0.20/0.52  fof(f556,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK3,k1_xboole_0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~spl8_51),
% 0.20/0.52    inference(superposition,[],[f102,f553])).
% 0.20/0.52  fof(f553,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) | ~spl8_51),
% 0.20/0.52    inference(avatar_component_clause,[],[f551])).
% 0.20/0.52  fof(f551,plain,(
% 0.20/0.52    spl8_51 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f554,plain,(
% 0.20/0.52    spl8_51 | ~spl8_45 | ~spl8_48),
% 0.20/0.52    inference(avatar_split_clause,[],[f549,f498,f470,f551])).
% 0.20/0.52  fof(f498,plain,(
% 0.20/0.52    spl8_48 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.20/0.52  fof(f549,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl8_45 | ~spl8_48)),
% 0.20/0.52    inference(forward_demodulation,[],[f490,f500])).
% 0.20/0.52  fof(f500,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK3) | ~spl8_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f498])).
% 0.20/0.52  fof(f490,plain,(
% 0.20/0.52    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | ~spl8_45),
% 0.20/0.52    inference(resolution,[],[f472,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f539,plain,(
% 0.20/0.52    spl8_50 | ~spl8_43 | ~spl8_47),
% 0.20/0.52    inference(avatar_split_clause,[],[f527,f480,f457,f535])).
% 0.20/0.52  fof(f535,plain,(
% 0.20/0.52    spl8_50 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.52  fof(f457,plain,(
% 0.20/0.52    spl8_43 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.20/0.52  fof(f480,plain,(
% 0.20/0.52    spl8_47 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.20/0.52  fof(f527,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_43 | ~spl8_47)),
% 0.20/0.52    inference(subsumption_resolution,[],[f513,f459])).
% 0.20/0.52  fof(f459,plain,(
% 0.20/0.52    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl8_43),
% 0.20/0.52    inference(avatar_component_clause,[],[f457])).
% 0.20/0.52  fof(f513,plain,(
% 0.20/0.52    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl8_47),
% 0.20/0.52    inference(resolution,[],[f482,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.52    inference(equality_resolution,[],[f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f54])).
% 0.20/0.52  fof(f482,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_47),
% 0.20/0.52    inference(avatar_component_clause,[],[f480])).
% 0.20/0.52  fof(f538,plain,(
% 0.20/0.52    ~spl8_50 | ~spl8_6 | ~spl8_7 | spl8_25),
% 0.20/0.52    inference(avatar_split_clause,[],[f508,f285,f141,f137,f535])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    spl8_6 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl8_7 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.52  fof(f285,plain,(
% 0.20/0.52    spl8_25 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.52  fof(f508,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_6 | ~spl8_7 | spl8_25)),
% 0.20/0.52    inference(forward_demodulation,[],[f507,f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl8_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f141])).
% 0.20/0.52  fof(f507,plain,(
% 0.20/0.52    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl8_6 | spl8_25)),
% 0.20/0.52    inference(forward_demodulation,[],[f286,f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl8_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f137])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    sK0 != k1_relset_1(sK0,sK1,sK3) | spl8_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f285])).
% 0.20/0.52  fof(f501,plain,(
% 0.20/0.52    spl8_48 | ~spl8_7 | ~spl8_26),
% 0.20/0.52    inference(avatar_split_clause,[],[f440,f300,f141,f498])).
% 0.20/0.52  fof(f300,plain,(
% 0.20/0.52    spl8_26 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.20/0.52  fof(f440,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK3) | (~spl8_7 | ~spl8_26)),
% 0.20/0.52    inference(backward_demodulation,[],[f302,f143])).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK3) | ~spl8_26),
% 0.20/0.52    inference(avatar_component_clause,[],[f300])).
% 0.20/0.52  fof(f483,plain,(
% 0.20/0.52    spl8_47 | ~spl8_5 | ~spl8_6 | ~spl8_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f468,f141,f137,f132,f480])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl8_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.52  fof(f468,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.20/0.52    inference(forward_demodulation,[],[f430,f143])).
% 0.20/0.52  fof(f430,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_5 | ~spl8_6)),
% 0.20/0.52    inference(backward_demodulation,[],[f134,f138])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f132])).
% 0.20/0.52  fof(f473,plain,(
% 0.20/0.52    spl8_45 | ~spl8_7 | ~spl8_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f467,f201,f141,f470])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    spl8_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.52  fof(f467,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (~spl8_7 | ~spl8_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f202,f143])).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl8_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f201])).
% 0.20/0.52  fof(f466,plain,(
% 0.20/0.52    spl8_43 | ~spl8_4 | ~spl8_6 | ~spl8_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f450,f141,f137,f127,f457])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    spl8_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f450,plain,(
% 0.20/0.52    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl8_4 | ~spl8_6 | ~spl8_7)),
% 0.20/0.52    inference(forward_demodulation,[],[f429,f143])).
% 0.20/0.52  fof(f429,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl8_4 | ~spl8_6)),
% 0.20/0.52    inference(backward_demodulation,[],[f129,f138])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    v1_funct_2(sK3,sK0,sK1) | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f127])).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    ~spl8_13 | spl8_15 | ~spl8_39),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f422])).
% 0.20/0.52  fof(f422,plain,(
% 0.20/0.52    $false | (~spl8_13 | spl8_15 | ~spl8_39)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f194,f408,f203,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (~sP6(X3,X2) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.20/0.52    inference(general_splitting,[],[f88,f107_D])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | sP6(X3,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f107_D])).
% 0.20/0.52  fof(f107_D,plain,(
% 0.20/0.52    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) <=> ~sP6(X3,X2)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.52    inference(flattening,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl8_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f201])).
% 0.20/0.52  fof(f408,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK3),sK2) | ~spl8_39),
% 0.20/0.52    inference(avatar_component_clause,[],[f407])).
% 0.20/0.52  fof(f407,plain,(
% 0.20/0.52    spl8_39 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    sP6(sK3,sK0) | ~spl8_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    spl8_13 <=> sP6(sK3,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.52  fof(f417,plain,(
% 0.20/0.52    ~spl8_2 | ~spl8_8 | ~spl8_12 | spl8_39),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f415])).
% 0.20/0.52  fof(f415,plain,(
% 0.20/0.52    $false | (~spl8_2 | ~spl8_8 | ~spl8_12 | spl8_39)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f119,f186,f150,f409,f182])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | r1_tarski(k2_relat_1(X5),X4) | ~v5_relat_1(X5,X3) | ~r1_tarski(X3,X4)) )),
% 0.20/0.52    inference(resolution,[],[f87,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.52  fof(f409,plain,(
% 0.20/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | spl8_39),
% 0.20/0.52    inference(avatar_component_clause,[],[f407])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    v1_relat_1(sK3) | ~spl8_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl8_8 <=> v1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    v5_relat_1(sK3,sK1) | ~spl8_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f184])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    spl8_12 <=> v5_relat_1(sK3,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2) | ~spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl8_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.52  fof(f410,plain,(
% 0.20/0.52    ~spl8_39 | spl8_14 | ~spl8_37),
% 0.20/0.52    inference(avatar_split_clause,[],[f401,f394,f197,f407])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    spl8_14 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.52  fof(f394,plain,(
% 0.20/0.52    spl8_37 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | v1_funct_2(sK3,sK0,X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | (spl8_14 | ~spl8_37)),
% 0.20/0.52    inference(resolution,[],[f395,f199])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ~v1_funct_2(sK3,sK0,sK2) | spl8_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f197])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_2(sK3,sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl8_37),
% 0.20/0.52    inference(avatar_component_clause,[],[f394])).
% 0.20/0.52  fof(f396,plain,(
% 0.20/0.52    spl8_37 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_31 | ~spl8_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f392,f382,f357,f137,f132,f127,f394])).
% 0.20/0.52  fof(f357,plain,(
% 0.20/0.52    spl8_31 <=> k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.20/0.52  fof(f382,plain,(
% 0.20/0.52    spl8_35 <=> ! [X1,X0,X2] : (k1_xboole_0 = X0 | ~r1_tarski(k2_relset_1(X1,X0,sK3),X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | v1_funct_2(sK3,X1,X2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.20/0.52  fof(f392,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | v1_funct_2(sK3,sK0,X0)) ) | (~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_31 | ~spl8_35)),
% 0.20/0.52    inference(forward_demodulation,[],[f391,f359])).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) | ~spl8_31),
% 0.20/0.52    inference(avatar_component_clause,[],[f357])).
% 0.20/0.52  fof(f391,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relset_1(sK0,sK1,sK3),X0) | v1_funct_2(sK3,sK0,X0)) ) | (~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_35)),
% 0.20/0.52    inference(subsumption_resolution,[],[f390,f129])).
% 0.20/0.52  fof(f390,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relset_1(sK0,sK1,sK3),X0) | ~v1_funct_2(sK3,sK0,sK1) | v1_funct_2(sK3,sK0,X0)) ) | (~spl8_5 | spl8_6 | ~spl8_35)),
% 0.20/0.52    inference(subsumption_resolution,[],[f389,f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl8_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f137])).
% 0.20/0.52  fof(f389,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relset_1(sK0,sK1,sK3),X0) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | v1_funct_2(sK3,sK0,X0)) ) | (~spl8_5 | ~spl8_35)),
% 0.20/0.52    inference(resolution,[],[f383,f134])).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k2_relset_1(X1,X0,sK3),X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | v1_funct_2(sK3,X1,X2)) ) | ~spl8_35),
% 0.20/0.52    inference(avatar_component_clause,[],[f382])).
% 0.20/0.52  fof(f384,plain,(
% 0.20/0.52    spl8_35 | ~spl8_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f266,f112,f382])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    spl8_1 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(k2_relset_1(X1,X0,sK3),X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | v1_funct_2(sK3,X1,X2)) ) | ~spl8_1),
% 0.20/0.52    inference(resolution,[],[f91,f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    v1_funct_1(sK3) | ~spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f112])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | v1_funct_2(X3,X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f39])).
% 0.20/0.52  % (13844)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (13827)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (13846)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (13845)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (13826)Refutation not found, incomplete strategy% (13826)------------------------------
% 0.20/0.52  % (13826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13826)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13826)Memory used [KB]: 10618
% 0.20/0.52  % (13826)Time elapsed: 0.114 s
% 0.20/0.52  % (13826)------------------------------
% 0.20/0.52  % (13826)------------------------------
% 0.20/0.53  % (13832)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (13831)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (13843)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.20/0.53  fof(f365,plain,(
% 0.20/0.53    spl8_31 | ~spl8_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f342,f132,f357])).
% 0.20/0.53  fof(f342,plain,(
% 0.20/0.53    k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f134,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f328,plain,(
% 0.20/0.53    ~spl8_28 | ~spl8_7 | spl8_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f310,f197,f141,f325])).
% 0.20/0.53  fof(f310,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl8_7 | spl8_14)),
% 0.20/0.53    inference(backward_demodulation,[],[f199,f143])).
% 0.20/0.53  fof(f303,plain,(
% 0.20/0.53    spl8_26 | ~spl8_5 | ~spl8_25),
% 0.20/0.53    inference(avatar_split_clause,[],[f298,f285,f132,f300])).
% 0.20/0.53  fof(f298,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | (~spl8_5 | ~spl8_25)),
% 0.20/0.53    inference(forward_demodulation,[],[f209,f287])).
% 0.20/0.53  fof(f287,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_25),
% 0.20/0.53    inference(avatar_component_clause,[],[f285])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f77,f134])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ~spl8_14 | ~spl8_15 | ~spl8_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f190,f112,f201,f197])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~spl8_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f60,f114])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f18])).
% 0.20/0.53  fof(f18,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    spl8_13 | ~spl8_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f188,f132,f192])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    sP6(sK3,sK0) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f107,f134])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    spl8_12 | ~spl8_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f174,f132,f184])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    v5_relat_1(sK3,sK1) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f80,f134])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    spl8_8 | ~spl8_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f146,f132,f148])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f76,f134])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ~spl8_6 | spl8_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f59,f141,f137])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl8_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f57,f132])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    spl8_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f56,f127])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f117])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    r1_tarski(sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    spl8_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f55,f112])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (13828)------------------------------
% 0.20/0.53  % (13828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13828)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (13828)Memory used [KB]: 6524
% 0.20/0.53  % (13828)Time elapsed: 0.109 s
% 0.20/0.53  % (13828)------------------------------
% 0.20/0.53  % (13828)------------------------------
% 0.20/0.53  % (13825)Success in time 0.174 s
%------------------------------------------------------------------------------
