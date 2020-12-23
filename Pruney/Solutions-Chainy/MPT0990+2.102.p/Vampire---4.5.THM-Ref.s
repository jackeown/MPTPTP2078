%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:46 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 426 expanded)
%              Number of leaves         :   43 ( 171 expanded)
%              Depth                    :   22
%              Number of atoms          :  984 (2428 expanded)
%              Number of equality atoms :  220 ( 676 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1098,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f182,f188,f197,f203,f303,f310,f320,f344,f356,f396,f406,f446,f475,f735,f867,f1097])).

fof(f1097,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1096])).

fof(f1096,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f1095])).

fof(f1095,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1094,f317])).

fof(f317,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl4_25
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1094,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1093,f196])).

fof(f196,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1093,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1092,f166])).

fof(f166,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1092,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1091,f126])).

fof(f126,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1091,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f1089])).

fof(f1089,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3))
    | k2_funct_1(sK2) = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36
    | ~ spl4_54 ),
    inference(superposition,[],[f1029,f734])).

fof(f734,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl4_54
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1029,plain,
    ( ! [X2] :
        ( k6_relat_1(sK0) != k5_relat_1(sK2,X2)
        | k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f1028,f353])).

fof(f353,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl4_27
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1028,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f1027,f141])).

fof(f141,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1027,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v2_funct_1(sK2) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_32
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f1026,f474])).

fof(f474,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl4_36
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f1026,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1025,f343])).

fof(f343,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl4_26
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1025,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1024,f202])).

fof(f202,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1024,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f1021,f181])).

fof(f181,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1021,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(sK2) )
    | ~ spl4_32 ),
    inference(duplicate_literal_removal,[],[f1016])).

fof(f1016,plain,
    ( ! [X2] :
        ( k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1)
        | k2_funct_1(sK2) = X2
        | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_32 ),
    inference(superposition,[],[f410,f445])).

fof(f445,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl4_32
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f410,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k2_funct_1(X3),X4) != k6_relat_1(k1_relat_1(X5))
      | k2_funct_1(X3) = X5
      | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(k2_funct_1(X3))
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f119,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f119,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

fof(f867,plain,
    ( ~ spl4_7
    | ~ spl4_10
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f865])).

fof(f865,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_10
    | spl4_53 ),
    inference(unit_resulting_resolution,[],[f171,f156,f730,f365])).

fof(f365,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f108,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f730,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f728])).

fof(f728,plain,
    ( spl4_53
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f156,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f171,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f735,plain,
    ( ~ spl4_53
    | spl4_54
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f716,f403,f732,f728])).

fof(f403,plain,
    ( spl4_30
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f716,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_30 ),
    inference(resolution,[],[f331,f405])).

fof(f405,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f403])).

fof(f331,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f92,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f475,plain,
    ( spl4_36
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f470,f393,f472])).

fof(f393,plain,
    ( spl4_29
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f470,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f452,f102])).

fof(f102,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f452,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_29 ),
    inference(resolution,[],[f395,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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

fof(f395,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f393])).

fof(f446,plain,
    ( spl4_32
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f441,f179,f174,f169,f149,f139,f129,f443])).

fof(f129,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f149,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f174,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f441,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f440,f181])).

fof(f440,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f439,f176])).

fof(f176,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f439,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f438,f171])).

fof(f438,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f437,f141])).

fof(f437,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f436,f131])).

fof(f131,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f436,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f417,f151])).

fof(f151,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f417,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f77,f94])).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f406,plain,
    ( spl4_30
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f401,f185,f179,f169,f164,f154,f403])).

fof(f185,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f401,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f400,f181])).

fof(f400,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f399,f171])).

fof(f399,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f398,f166])).

fof(f398,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f397,f156])).

fof(f397,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f187,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f187,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f396,plain,
    ( spl4_29
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f391,f179,f174,f169,f149,f139,f393])).

fof(f391,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f390,f181])).

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f389,f176])).

fof(f389,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f388,f171])).

fof(f388,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f387,f141])).

fof(f387,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f384])).

fof(f384,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f80,f151])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f356,plain,
    ( spl4_27
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f355,f307,f169,f351])).

fof(f307,plain,
    ( spl4_24
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f355,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f347,f171])).

fof(f347,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_24 ),
    inference(superposition,[],[f105,f309])).

fof(f309,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f307])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f344,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f339,f179,f174,f169,f149,f139,f341])).

fof(f339,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f338,f181])).

fof(f338,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f337,f176])).

fof(f337,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f336,f171])).

fof(f336,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f335,f141])).

fof(f335,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f332])).

fof(f332,plain,
    ( sK1 != sK1
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f78,f151])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f320,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f319,f300,f154,f315])).

fof(f300,plain,
    ( spl4_23
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f319,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f312,f156])).

fof(f312,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_23 ),
    inference(superposition,[],[f105,f302])).

fof(f302,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f300])).

fof(f310,plain,
    ( spl4_24
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f305,f174,f169,f129,f307])).

fof(f305,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f304,f131])).

fof(f304,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f295,f176])).

fof(f295,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f85,f171])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f303,plain,
    ( spl4_23
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f298,f159,f154,f134,f300])).

fof(f134,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f159,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f298,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f297,f136])).

fof(f136,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f297,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f294,f161])).

fof(f161,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f294,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f85,f156])).

fof(f203,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f198,f169,f200])).

fof(f198,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f190,f102])).

fof(f190,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f100,f171])).

fof(f197,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f192,f154,f194])).

fof(f192,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f189,f102])).

fof(f189,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f100,f156])).

fof(f188,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f183,f144,f185])).

fof(f144,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f183,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f146,f94])).

fof(f146,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f182,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f64,f179])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f57,f56])).

fof(f56,plain,
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

fof(f57,plain,
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f177,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f65,f174])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f172,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f66,f169])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f167,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f67,f164])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f162,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f68,f159])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f157,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f69,f154])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f152,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f70,f149])).

fof(f70,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f147,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f71,f144])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f142,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f72,f139])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f137,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f73,f134])).

fof(f73,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f58])).

fof(f132,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f74,f129])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f58])).

fof(f127,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f75,f124])).

fof(f75,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (12285)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12311)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (12304)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (12291)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12297)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (12293)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (12287)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (12286)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (12288)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (12308)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (12300)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (12303)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (12292)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (12286)Refutation not found, incomplete strategy% (12286)------------------------------
% 0.21/0.54  % (12286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12294)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (12312)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (12286)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12286)Memory used [KB]: 1791
% 0.21/0.54  % (12286)Time elapsed: 0.127 s
% 0.21/0.54  % (12286)------------------------------
% 0.21/0.54  % (12286)------------------------------
% 0.21/0.54  % (12314)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (12314)Refutation not found, incomplete strategy% (12314)------------------------------
% 0.21/0.55  % (12314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12314)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12314)Memory used [KB]: 1791
% 0.21/0.55  % (12314)Time elapsed: 0.104 s
% 0.21/0.55  % (12314)------------------------------
% 0.21/0.55  % (12314)------------------------------
% 0.21/0.55  % (12289)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (12310)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (12302)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (12296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (12299)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (12301)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (12305)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (12304)Refutation not found, incomplete strategy% (12304)------------------------------
% 0.21/0.55  % (12304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12304)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12304)Memory used [KB]: 2174
% 0.21/0.55  % (12304)Time elapsed: 0.154 s
% 0.21/0.55  % (12304)------------------------------
% 0.21/0.55  % (12304)------------------------------
% 0.21/0.55  % (12301)Refutation not found, incomplete strategy% (12301)------------------------------
% 0.21/0.55  % (12301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12290)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (12301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12301)Memory used [KB]: 10746
% 0.21/0.56  % (12301)Time elapsed: 0.137 s
% 0.21/0.56  % (12301)------------------------------
% 0.21/0.56  % (12301)------------------------------
% 0.21/0.56  % (12295)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (12313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (12298)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (12307)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.58  % (12306)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.58  % (12299)Refutation not found, incomplete strategy% (12299)------------------------------
% 0.21/0.58  % (12299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12299)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12299)Memory used [KB]: 2046
% 0.21/0.58  % (12299)Time elapsed: 0.123 s
% 0.21/0.58  % (12299)------------------------------
% 0.21/0.58  % (12299)------------------------------
% 0.21/0.58  % (12309)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.59  % (12311)Refutation not found, incomplete strategy% (12311)------------------------------
% 0.21/0.59  % (12311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (12311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (12311)Memory used [KB]: 6908
% 0.21/0.59  % (12311)Time elapsed: 0.179 s
% 0.21/0.59  % (12311)------------------------------
% 0.21/0.59  % (12311)------------------------------
% 1.81/0.60  % (12312)Refutation not found, incomplete strategy% (12312)------------------------------
% 1.81/0.60  % (12312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (12312)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (12312)Memory used [KB]: 6652
% 1.81/0.61  % (12312)Time elapsed: 0.181 s
% 1.81/0.61  % (12312)------------------------------
% 1.81/0.61  % (12312)------------------------------
% 1.81/0.62  % (12309)Refutation not found, incomplete strategy% (12309)------------------------------
% 1.81/0.62  % (12309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (12309)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.62  
% 1.81/0.62  % (12309)Memory used [KB]: 11001
% 1.81/0.62  % (12309)Time elapsed: 0.217 s
% 1.81/0.62  % (12309)------------------------------
% 1.81/0.62  % (12309)------------------------------
% 2.01/0.64  % (12306)Refutation found. Thanks to Tanya!
% 2.01/0.64  % SZS status Theorem for theBenchmark
% 2.01/0.64  % SZS output start Proof for theBenchmark
% 2.01/0.64  fof(f1098,plain,(
% 2.01/0.64    $false),
% 2.01/0.64    inference(avatar_sat_refutation,[],[f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f182,f188,f197,f203,f303,f310,f320,f344,f356,f396,f406,f446,f475,f735,f867,f1097])).
% 2.01/0.64  fof(f1097,plain,(
% 2.01/0.64    spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f1096])).
% 2.01/0.64  fof(f1096,plain,(
% 2.01/0.64    $false | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(trivial_inequality_removal,[],[f1095])).
% 2.01/0.64  fof(f1095,plain,(
% 2.01/0.64    k6_relat_1(sK1) != k6_relat_1(sK1) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(forward_demodulation,[],[f1094,f317])).
% 2.01/0.64  fof(f317,plain,(
% 2.01/0.64    sK1 = k1_relat_1(sK3) | ~spl4_25),
% 2.01/0.64    inference(avatar_component_clause,[],[f315])).
% 2.01/0.64  fof(f315,plain,(
% 2.01/0.64    spl4_25 <=> sK1 = k1_relat_1(sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.01/0.64  fof(f1094,plain,(
% 2.01/0.64    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1093,f196])).
% 2.01/0.64  fof(f196,plain,(
% 2.01/0.64    v1_relat_1(sK3) | ~spl4_14),
% 2.01/0.64    inference(avatar_component_clause,[],[f194])).
% 2.01/0.64  fof(f194,plain,(
% 2.01/0.64    spl4_14 <=> v1_relat_1(sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.01/0.64  fof(f1093,plain,(
% 2.01/0.64    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1092,f166])).
% 2.01/0.64  fof(f166,plain,(
% 2.01/0.64    v1_funct_1(sK3) | ~spl4_9),
% 2.01/0.64    inference(avatar_component_clause,[],[f164])).
% 2.01/0.64  fof(f164,plain,(
% 2.01/0.64    spl4_9 <=> v1_funct_1(sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.01/0.64  fof(f1092,plain,(
% 2.01/0.64    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1091,f126])).
% 2.01/0.64  fof(f126,plain,(
% 2.01/0.64    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.01/0.64    inference(avatar_component_clause,[],[f124])).
% 2.01/0.64  fof(f124,plain,(
% 2.01/0.64    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.01/0.64  fof(f1091,plain,(
% 2.01/0.64    k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(trivial_inequality_removal,[],[f1089])).
% 2.01/0.64  fof(f1089,plain,(
% 2.01/0.64    k6_relat_1(sK0) != k6_relat_1(sK0) | k6_relat_1(sK1) != k6_relat_1(k1_relat_1(sK3)) | k2_funct_1(sK2) = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36 | ~spl4_54)),
% 2.01/0.64    inference(superposition,[],[f1029,f734])).
% 2.01/0.64  fof(f734,plain,(
% 2.01/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_54),
% 2.01/0.64    inference(avatar_component_clause,[],[f732])).
% 2.01/0.64  fof(f732,plain,(
% 2.01/0.64    spl4_54 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.01/0.64  fof(f1029,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(sK0) != k5_relat_1(sK2,X2) | k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_27 | ~spl4_32 | ~spl4_36)),
% 2.01/0.64    inference(forward_demodulation,[],[f1028,f353])).
% 2.01/0.64  fof(f353,plain,(
% 2.01/0.64    sK0 = k1_relat_1(sK2) | ~spl4_27),
% 2.01/0.64    inference(avatar_component_clause,[],[f351])).
% 2.01/0.64  fof(f351,plain,(
% 2.01/0.64    spl4_27 <=> sK0 = k1_relat_1(sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.01/0.64  fof(f1028,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_32 | ~spl4_36)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1027,f141])).
% 2.01/0.64  fof(f141,plain,(
% 2.01/0.64    v2_funct_1(sK2) | ~spl4_4),
% 2.01/0.64    inference(avatar_component_clause,[],[f139])).
% 2.01/0.64  fof(f139,plain,(
% 2.01/0.64    spl4_4 <=> v2_funct_1(sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.01/0.64  fof(f1027,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v2_funct_1(sK2)) ) | (~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_32 | ~spl4_36)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1026,f474])).
% 2.01/0.64  fof(f474,plain,(
% 2.01/0.64    v1_relat_1(k2_funct_1(sK2)) | ~spl4_36),
% 2.01/0.64    inference(avatar_component_clause,[],[f472])).
% 2.01/0.64  fof(f472,plain,(
% 2.01/0.64    spl4_36 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.01/0.64  fof(f1026,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2)) ) | (~spl4_12 | ~spl4_15 | ~spl4_26 | ~spl4_32)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1025,f343])).
% 2.01/0.64  fof(f343,plain,(
% 2.01/0.64    v1_funct_1(k2_funct_1(sK2)) | ~spl4_26),
% 2.01/0.64    inference(avatar_component_clause,[],[f341])).
% 2.01/0.64  fof(f341,plain,(
% 2.01/0.64    spl4_26 <=> v1_funct_1(k2_funct_1(sK2))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.01/0.64  fof(f1025,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2)) ) | (~spl4_12 | ~spl4_15 | ~spl4_32)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1024,f202])).
% 2.01/0.64  fof(f202,plain,(
% 2.01/0.64    v1_relat_1(sK2) | ~spl4_15),
% 2.01/0.64    inference(avatar_component_clause,[],[f200])).
% 2.01/0.64  fof(f200,plain,(
% 2.01/0.64    spl4_15 <=> v1_relat_1(sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.01/0.64  fof(f1024,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2)) ) | (~spl4_12 | ~spl4_32)),
% 2.01/0.64    inference(subsumption_resolution,[],[f1021,f181])).
% 2.01/0.64  fof(f181,plain,(
% 2.01/0.64    v1_funct_1(sK2) | ~spl4_12),
% 2.01/0.64    inference(avatar_component_clause,[],[f179])).
% 2.01/0.64  fof(f179,plain,(
% 2.01/0.64    spl4_12 <=> v1_funct_1(sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.01/0.64  fof(f1021,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2)) ) | ~spl4_32),
% 2.01/0.64    inference(duplicate_literal_removal,[],[f1016])).
% 2.01/0.64  fof(f1016,plain,(
% 2.01/0.64    ( ! [X2] : (k6_relat_1(k1_relat_1(X2)) != k6_relat_1(sK1) | k2_funct_1(sK2) = X2 | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_32),
% 2.01/0.64    inference(superposition,[],[f410,f445])).
% 2.01/0.64  fof(f445,plain,(
% 2.01/0.64    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_32),
% 2.01/0.64    inference(avatar_component_clause,[],[f443])).
% 2.01/0.64  fof(f443,plain,(
% 2.01/0.64    spl4_32 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.01/0.64  fof(f410,plain,(
% 2.01/0.64    ( ! [X4,X5,X3] : (k5_relat_1(k2_funct_1(X3),X4) != k6_relat_1(k1_relat_1(X5)) | k2_funct_1(X3) = X5 | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(k2_funct_1(X3)) | ~v1_relat_1(k2_funct_1(X3)) | ~v2_funct_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.01/0.64    inference(superposition,[],[f119,f84])).
% 2.01/0.64  fof(f84,plain,(
% 2.01/0.64    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f35])).
% 2.01/0.64  fof(f35,plain,(
% 2.01/0.64    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(flattening,[],[f34])).
% 2.01/0.64  fof(f34,plain,(
% 2.01/0.64    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.64    inference(ennf_transformation,[],[f9])).
% 2.01/0.64  fof(f9,axiom,(
% 2.01/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.01/0.64  fof(f119,plain,(
% 2.01/0.64    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(equality_resolution,[],[f97])).
% 2.15/0.66  fof(f97,plain,(
% 2.15/0.66    ( ! [X2,X0,X3,X1] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f46])).
% 2.15/0.66  fof(f46,plain,(
% 2.15/0.66    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.15/0.66    inference(flattening,[],[f45])).
% 2.15/0.66  fof(f45,plain,(
% 2.15/0.66    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.15/0.66    inference(ennf_transformation,[],[f7])).
% 2.15/0.66  fof(f7,axiom,(
% 2.15/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).
% 2.15/0.66  fof(f867,plain,(
% 2.15/0.66    ~spl4_7 | ~spl4_10 | spl4_53),
% 2.15/0.66    inference(avatar_contradiction_clause,[],[f865])).
% 2.15/0.66  fof(f865,plain,(
% 2.15/0.66    $false | (~spl4_7 | ~spl4_10 | spl4_53)),
% 2.15/0.66    inference(unit_resulting_resolution,[],[f171,f156,f730,f365])).
% 2.15/0.66  fof(f365,plain,(
% 2.15/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.66    inference(duplicate_literal_removal,[],[f364])).
% 2.15/0.66  fof(f364,plain,(
% 2.15/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.66    inference(superposition,[],[f108,f103])).
% 2.15/0.66  fof(f103,plain,(
% 2.15/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f49])).
% 2.15/0.66  fof(f49,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(flattening,[],[f48])).
% 2.15/0.66  fof(f48,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.15/0.66    inference(ennf_transformation,[],[f15])).
% 2.15/0.66  fof(f15,axiom,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 2.15/0.66  fof(f108,plain,(
% 2.15/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f54])).
% 2.15/0.66  fof(f54,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(flattening,[],[f53])).
% 2.15/0.66  fof(f53,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.15/0.66    inference(ennf_transformation,[],[f12])).
% 2.15/0.66  fof(f12,axiom,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 2.15/0.66  fof(f730,plain,(
% 2.15/0.66    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_53),
% 2.15/0.66    inference(avatar_component_clause,[],[f728])).
% 2.15/0.66  fof(f728,plain,(
% 2.15/0.66    spl4_53 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.15/0.66  fof(f156,plain,(
% 2.15/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.15/0.66    inference(avatar_component_clause,[],[f154])).
% 2.15/0.66  fof(f154,plain,(
% 2.15/0.66    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.15/0.66  fof(f171,plain,(
% 2.15/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.15/0.66    inference(avatar_component_clause,[],[f169])).
% 2.15/0.66  fof(f169,plain,(
% 2.15/0.66    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.15/0.66  fof(f735,plain,(
% 2.15/0.66    ~spl4_53 | spl4_54 | ~spl4_30),
% 2.15/0.66    inference(avatar_split_clause,[],[f716,f403,f732,f728])).
% 2.15/0.66  fof(f403,plain,(
% 2.15/0.66    spl4_30 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.15/0.66  fof(f716,plain,(
% 2.15/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_30),
% 2.15/0.66    inference(resolution,[],[f331,f405])).
% 2.15/0.66  fof(f405,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_30),
% 2.15/0.66    inference(avatar_component_clause,[],[f403])).
% 2.15/0.66  fof(f331,plain,(
% 2.15/0.66    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.15/0.66    inference(resolution,[],[f92,f101])).
% 2.15/0.66  fof(f101,plain,(
% 2.15/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f17])).
% 2.15/0.66  fof(f17,axiom,(
% 2.15/0.66    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.15/0.66  fof(f92,plain,(
% 2.15/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f60])).
% 2.15/0.66  fof(f60,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(nnf_transformation,[],[f41])).
% 2.15/0.66  fof(f41,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(flattening,[],[f40])).
% 2.15/0.66  fof(f40,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.15/0.66    inference(ennf_transformation,[],[f16])).
% 2.15/0.66  fof(f16,axiom,(
% 2.15/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.15/0.66  fof(f475,plain,(
% 2.15/0.66    spl4_36 | ~spl4_29),
% 2.15/0.66    inference(avatar_split_clause,[],[f470,f393,f472])).
% 2.15/0.66  fof(f393,plain,(
% 2.15/0.66    spl4_29 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.15/0.66  fof(f470,plain,(
% 2.15/0.66    v1_relat_1(k2_funct_1(sK2)) | ~spl4_29),
% 2.15/0.66    inference(subsumption_resolution,[],[f452,f102])).
% 2.15/0.66  fof(f102,plain,(
% 2.15/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f4])).
% 2.15/0.66  fof(f4,axiom,(
% 2.15/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.15/0.66  fof(f452,plain,(
% 2.15/0.66    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_29),
% 2.15/0.66    inference(resolution,[],[f395,f100])).
% 2.15/0.66  fof(f100,plain,(
% 2.15/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f47])).
% 2.15/0.66  fof(f47,plain,(
% 2.15/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.15/0.66    inference(ennf_transformation,[],[f2])).
% 2.15/0.66  fof(f2,axiom,(
% 2.15/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.15/0.66  fof(f395,plain,(
% 2.15/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_29),
% 2.15/0.66    inference(avatar_component_clause,[],[f393])).
% 2.15/0.66  fof(f446,plain,(
% 2.15/0.66    spl4_32 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.15/0.66    inference(avatar_split_clause,[],[f441,f179,f174,f169,f149,f139,f129,f443])).
% 2.15/0.66  fof(f129,plain,(
% 2.15/0.66    spl4_2 <=> k1_xboole_0 = sK1),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.15/0.66  fof(f149,plain,(
% 2.15/0.66    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.15/0.66  fof(f174,plain,(
% 2.15/0.66    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.15/0.66  fof(f441,plain,(
% 2.15/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.15/0.66    inference(subsumption_resolution,[],[f440,f181])).
% 2.15/0.66  fof(f440,plain,(
% 2.15/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.15/0.66    inference(subsumption_resolution,[],[f439,f176])).
% 2.15/0.66  fof(f176,plain,(
% 2.15/0.66    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.15/0.66    inference(avatar_component_clause,[],[f174])).
% 2.15/0.66  fof(f439,plain,(
% 2.15/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.15/0.66    inference(subsumption_resolution,[],[f438,f171])).
% 2.15/0.66  fof(f438,plain,(
% 2.15/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 2.15/0.66    inference(subsumption_resolution,[],[f437,f141])).
% 2.15/0.66  fof(f437,plain,(
% 2.15/0.66    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 2.15/0.66    inference(subsumption_resolution,[],[f436,f131])).
% 2.15/0.66  fof(f131,plain,(
% 2.15/0.66    k1_xboole_0 != sK1 | spl4_2),
% 2.15/0.66    inference(avatar_component_clause,[],[f129])).
% 2.15/0.66  fof(f436,plain,(
% 2.15/0.66    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.15/0.66    inference(trivial_inequality_removal,[],[f433])).
% 2.15/0.66  fof(f433,plain,(
% 2.15/0.66    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.15/0.66    inference(superposition,[],[f417,f151])).
% 2.15/0.66  fof(f151,plain,(
% 2.15/0.66    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.15/0.66    inference(avatar_component_clause,[],[f149])).
% 2.15/0.66  fof(f417,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.15/0.66    inference(forward_demodulation,[],[f77,f94])).
% 2.15/0.66  fof(f94,plain,(
% 2.15/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f20])).
% 2.15/0.66  fof(f20,axiom,(
% 2.15/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.15/0.66  fof(f77,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f29])).
% 2.15/0.66  fof(f29,plain,(
% 2.15/0.66    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.15/0.66    inference(flattening,[],[f28])).
% 2.15/0.66  fof(f28,plain,(
% 2.15/0.66    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.15/0.66    inference(ennf_transformation,[],[f22])).
% 2.15/0.66  fof(f22,axiom,(
% 2.15/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.15/0.66  fof(f406,plain,(
% 2.15/0.66    spl4_30 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.15/0.66    inference(avatar_split_clause,[],[f401,f185,f179,f169,f164,f154,f403])).
% 2.15/0.66  fof(f185,plain,(
% 2.15/0.66    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.15/0.66  fof(f401,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.15/0.66    inference(subsumption_resolution,[],[f400,f181])).
% 2.15/0.66  fof(f400,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.15/0.66    inference(subsumption_resolution,[],[f399,f171])).
% 2.15/0.66  fof(f399,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.15/0.66    inference(subsumption_resolution,[],[f398,f166])).
% 2.15/0.66  fof(f398,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.15/0.66    inference(subsumption_resolution,[],[f397,f156])).
% 2.15/0.66  fof(f397,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.15/0.66    inference(superposition,[],[f187,f95])).
% 2.15/0.66  fof(f95,plain,(
% 2.15/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f43])).
% 2.15/0.66  fof(f43,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.15/0.66    inference(flattening,[],[f42])).
% 2.15/0.66  fof(f42,plain,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.15/0.66    inference(ennf_transformation,[],[f19])).
% 2.15/0.66  fof(f19,axiom,(
% 2.15/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.15/0.66  fof(f187,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.15/0.66    inference(avatar_component_clause,[],[f185])).
% 2.15/0.66  fof(f396,plain,(
% 2.15/0.66    spl4_29 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.15/0.66    inference(avatar_split_clause,[],[f391,f179,f174,f169,f149,f139,f393])).
% 2.15/0.66  fof(f391,plain,(
% 2.15/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.15/0.66    inference(subsumption_resolution,[],[f390,f181])).
% 2.15/0.66  fof(f390,plain,(
% 2.15/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.15/0.66    inference(subsumption_resolution,[],[f389,f176])).
% 2.15/0.66  fof(f389,plain,(
% 2.15/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.15/0.66    inference(subsumption_resolution,[],[f388,f171])).
% 2.15/0.66  fof(f388,plain,(
% 2.15/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 2.15/0.66    inference(subsumption_resolution,[],[f387,f141])).
% 2.15/0.66  fof(f387,plain,(
% 2.15/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.15/0.66    inference(trivial_inequality_removal,[],[f384])).
% 2.15/0.66  fof(f384,plain,(
% 2.15/0.66    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.15/0.66    inference(superposition,[],[f80,f151])).
% 2.15/0.66  fof(f80,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f31])).
% 2.15/0.66  fof(f31,plain,(
% 2.15/0.66    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.15/0.66    inference(flattening,[],[f30])).
% 2.15/0.66  fof(f30,plain,(
% 2.15/0.66    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.15/0.66    inference(ennf_transformation,[],[f21])).
% 2.15/0.66  fof(f21,axiom,(
% 2.15/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.15/0.66  fof(f356,plain,(
% 2.15/0.66    spl4_27 | ~spl4_10 | ~spl4_24),
% 2.15/0.66    inference(avatar_split_clause,[],[f355,f307,f169,f351])).
% 2.15/0.66  fof(f307,plain,(
% 2.15/0.66    spl4_24 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.15/0.66  fof(f355,plain,(
% 2.15/0.66    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_24)),
% 2.15/0.66    inference(subsumption_resolution,[],[f347,f171])).
% 2.15/0.66  fof(f347,plain,(
% 2.15/0.66    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_24),
% 2.15/0.66    inference(superposition,[],[f105,f309])).
% 2.15/0.66  fof(f309,plain,(
% 2.15/0.66    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_24),
% 2.15/0.66    inference(avatar_component_clause,[],[f307])).
% 2.15/0.66  fof(f105,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.66    inference(cnf_transformation,[],[f51])).
% 2.15/0.66  fof(f51,plain,(
% 2.15/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(ennf_transformation,[],[f13])).
% 2.15/0.66  fof(f13,axiom,(
% 2.15/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.15/0.66  fof(f344,plain,(
% 2.15/0.66    spl4_26 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.15/0.66    inference(avatar_split_clause,[],[f339,f179,f174,f169,f149,f139,f341])).
% 2.15/0.66  fof(f339,plain,(
% 2.15/0.66    v1_funct_1(k2_funct_1(sK2)) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.15/0.66    inference(subsumption_resolution,[],[f338,f181])).
% 2.15/0.66  fof(f338,plain,(
% 2.15/0.66    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.15/0.66    inference(subsumption_resolution,[],[f337,f176])).
% 2.15/0.66  fof(f337,plain,(
% 2.15/0.66    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.15/0.66    inference(subsumption_resolution,[],[f336,f171])).
% 2.15/0.66  fof(f336,plain,(
% 2.15/0.66    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 2.15/0.66    inference(subsumption_resolution,[],[f335,f141])).
% 2.15/0.66  fof(f335,plain,(
% 2.15/0.66    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.15/0.66    inference(trivial_inequality_removal,[],[f332])).
% 2.15/0.66  fof(f332,plain,(
% 2.15/0.66    sK1 != sK1 | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.15/0.66    inference(superposition,[],[f78,f151])).
% 2.15/0.66  fof(f78,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.15/0.66    inference(cnf_transformation,[],[f31])).
% 2.15/0.66  fof(f320,plain,(
% 2.15/0.66    spl4_25 | ~spl4_7 | ~spl4_23),
% 2.15/0.66    inference(avatar_split_clause,[],[f319,f300,f154,f315])).
% 2.15/0.66  fof(f300,plain,(
% 2.15/0.66    spl4_23 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.15/0.66  fof(f319,plain,(
% 2.15/0.66    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_23)),
% 2.15/0.66    inference(subsumption_resolution,[],[f312,f156])).
% 2.15/0.66  fof(f312,plain,(
% 2.15/0.66    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_23),
% 2.15/0.66    inference(superposition,[],[f105,f302])).
% 2.15/0.66  fof(f302,plain,(
% 2.15/0.66    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_23),
% 2.15/0.66    inference(avatar_component_clause,[],[f300])).
% 2.15/0.66  fof(f310,plain,(
% 2.15/0.66    spl4_24 | spl4_2 | ~spl4_10 | ~spl4_11),
% 2.15/0.66    inference(avatar_split_clause,[],[f305,f174,f169,f129,f307])).
% 2.15/0.66  fof(f305,plain,(
% 2.15/0.66    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.15/0.66    inference(subsumption_resolution,[],[f304,f131])).
% 2.15/0.66  fof(f304,plain,(
% 2.15/0.66    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 2.15/0.66    inference(subsumption_resolution,[],[f295,f176])).
% 2.15/0.66  fof(f295,plain,(
% 2.15/0.66    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 2.15/0.66    inference(resolution,[],[f85,f171])).
% 2.15/0.66  fof(f85,plain,(
% 2.15/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.15/0.66    inference(cnf_transformation,[],[f59])).
% 2.15/0.66  fof(f59,plain,(
% 2.15/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(nnf_transformation,[],[f37])).
% 2.15/0.66  fof(f37,plain,(
% 2.15/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(flattening,[],[f36])).
% 2.15/0.66  fof(f36,plain,(
% 2.15/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.66    inference(ennf_transformation,[],[f18])).
% 2.15/0.66  fof(f18,axiom,(
% 2.15/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.15/0.66  fof(f303,plain,(
% 2.15/0.66    spl4_23 | spl4_3 | ~spl4_7 | ~spl4_8),
% 2.15/0.66    inference(avatar_split_clause,[],[f298,f159,f154,f134,f300])).
% 2.15/0.66  fof(f134,plain,(
% 2.15/0.66    spl4_3 <=> k1_xboole_0 = sK0),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.15/0.66  fof(f159,plain,(
% 2.15/0.66    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.15/0.66  fof(f298,plain,(
% 2.15/0.66    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 2.15/0.66    inference(subsumption_resolution,[],[f297,f136])).
% 2.15/0.66  fof(f136,plain,(
% 2.15/0.66    k1_xboole_0 != sK0 | spl4_3),
% 2.15/0.66    inference(avatar_component_clause,[],[f134])).
% 2.15/0.66  fof(f297,plain,(
% 2.15/0.66    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 2.15/0.66    inference(subsumption_resolution,[],[f294,f161])).
% 2.15/0.66  fof(f161,plain,(
% 2.15/0.66    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.15/0.66    inference(avatar_component_clause,[],[f159])).
% 2.15/0.66  fof(f294,plain,(
% 2.15/0.66    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 2.15/0.66    inference(resolution,[],[f85,f156])).
% 2.15/0.66  fof(f203,plain,(
% 2.15/0.66    spl4_15 | ~spl4_10),
% 2.15/0.66    inference(avatar_split_clause,[],[f198,f169,f200])).
% 2.15/0.66  fof(f198,plain,(
% 2.15/0.66    v1_relat_1(sK2) | ~spl4_10),
% 2.15/0.66    inference(subsumption_resolution,[],[f190,f102])).
% 2.15/0.66  fof(f190,plain,(
% 2.15/0.66    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.15/0.66    inference(resolution,[],[f100,f171])).
% 2.15/0.66  fof(f197,plain,(
% 2.15/0.66    spl4_14 | ~spl4_7),
% 2.15/0.66    inference(avatar_split_clause,[],[f192,f154,f194])).
% 2.15/0.66  fof(f192,plain,(
% 2.15/0.66    v1_relat_1(sK3) | ~spl4_7),
% 2.15/0.66    inference(subsumption_resolution,[],[f189,f102])).
% 2.15/0.66  fof(f189,plain,(
% 2.15/0.66    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.15/0.66    inference(resolution,[],[f100,f156])).
% 2.15/0.66  fof(f188,plain,(
% 2.15/0.66    spl4_13 | ~spl4_5),
% 2.15/0.66    inference(avatar_split_clause,[],[f183,f144,f185])).
% 2.15/0.66  fof(f144,plain,(
% 2.15/0.66    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.15/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.15/0.66  fof(f183,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.15/0.66    inference(backward_demodulation,[],[f146,f94])).
% 2.15/0.66  fof(f146,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.15/0.66    inference(avatar_component_clause,[],[f144])).
% 2.15/0.66  fof(f182,plain,(
% 2.15/0.66    spl4_12),
% 2.15/0.66    inference(avatar_split_clause,[],[f64,f179])).
% 2.15/0.66  fof(f64,plain,(
% 2.15/0.66    v1_funct_1(sK2)),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f58,plain,(
% 2.15/0.66    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f57,f56])).
% 2.15/0.66  fof(f56,plain,(
% 2.15/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.15/0.66    introduced(choice_axiom,[])).
% 2.15/0.66  fof(f57,plain,(
% 2.15/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.15/0.66    introduced(choice_axiom,[])).
% 2.15/0.66  fof(f27,plain,(
% 2.15/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.15/0.66    inference(flattening,[],[f26])).
% 2.15/0.66  fof(f26,plain,(
% 2.15/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.15/0.66    inference(ennf_transformation,[],[f24])).
% 2.15/0.66  fof(f24,negated_conjecture,(
% 2.15/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.15/0.66    inference(negated_conjecture,[],[f23])).
% 2.15/0.66  fof(f23,conjecture,(
% 2.15/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.15/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.15/0.66  fof(f177,plain,(
% 2.15/0.66    spl4_11),
% 2.15/0.66    inference(avatar_split_clause,[],[f65,f174])).
% 2.15/0.66  fof(f65,plain,(
% 2.15/0.66    v1_funct_2(sK2,sK0,sK1)),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f172,plain,(
% 2.15/0.66    spl4_10),
% 2.15/0.66    inference(avatar_split_clause,[],[f66,f169])).
% 2.15/0.66  fof(f66,plain,(
% 2.15/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f167,plain,(
% 2.15/0.66    spl4_9),
% 2.15/0.66    inference(avatar_split_clause,[],[f67,f164])).
% 2.15/0.66  fof(f67,plain,(
% 2.15/0.66    v1_funct_1(sK3)),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f162,plain,(
% 2.15/0.66    spl4_8),
% 2.15/0.66    inference(avatar_split_clause,[],[f68,f159])).
% 2.15/0.66  fof(f68,plain,(
% 2.15/0.66    v1_funct_2(sK3,sK1,sK0)),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f157,plain,(
% 2.15/0.66    spl4_7),
% 2.15/0.66    inference(avatar_split_clause,[],[f69,f154])).
% 2.15/0.66  fof(f69,plain,(
% 2.15/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f152,plain,(
% 2.15/0.66    spl4_6),
% 2.15/0.66    inference(avatar_split_clause,[],[f70,f149])).
% 2.15/0.66  fof(f70,plain,(
% 2.15/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f147,plain,(
% 2.15/0.66    spl4_5),
% 2.15/0.66    inference(avatar_split_clause,[],[f71,f144])).
% 2.15/0.66  fof(f71,plain,(
% 2.15/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f142,plain,(
% 2.15/0.66    spl4_4),
% 2.15/0.66    inference(avatar_split_clause,[],[f72,f139])).
% 2.15/0.66  fof(f72,plain,(
% 2.15/0.66    v2_funct_1(sK2)),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f137,plain,(
% 2.15/0.66    ~spl4_3),
% 2.15/0.66    inference(avatar_split_clause,[],[f73,f134])).
% 2.15/0.66  fof(f73,plain,(
% 2.15/0.66    k1_xboole_0 != sK0),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f132,plain,(
% 2.15/0.66    ~spl4_2),
% 2.15/0.66    inference(avatar_split_clause,[],[f74,f129])).
% 2.15/0.66  fof(f74,plain,(
% 2.15/0.66    k1_xboole_0 != sK1),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  fof(f127,plain,(
% 2.15/0.66    ~spl4_1),
% 2.15/0.66    inference(avatar_split_clause,[],[f75,f124])).
% 2.15/0.66  fof(f75,plain,(
% 2.15/0.66    k2_funct_1(sK2) != sK3),
% 2.15/0.66    inference(cnf_transformation,[],[f58])).
% 2.15/0.66  % SZS output end Proof for theBenchmark
% 2.15/0.66  % (12306)------------------------------
% 2.15/0.66  % (12306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.66  % (12306)Termination reason: Refutation
% 2.15/0.66  
% 2.15/0.66  % (12306)Memory used [KB]: 7036
% 2.15/0.66  % (12306)Time elapsed: 0.235 s
% 2.15/0.66  % (12306)------------------------------
% 2.15/0.66  % (12306)------------------------------
% 2.15/0.66  % (12284)Success in time 0.303 s
%------------------------------------------------------------------------------
