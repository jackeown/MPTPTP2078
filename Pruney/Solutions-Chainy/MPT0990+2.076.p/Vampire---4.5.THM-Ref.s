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
% DateTime   : Thu Dec  3 13:02:41 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  361 ( 867 expanded)
%              Number of leaves         :   70 ( 379 expanded)
%              Depth                    :   16
%              Number of atoms          : 1785 (3988 expanded)
%              Number of equality atoms :  299 ( 897 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f176,f185,f190,f201,f221,f259,f285,f295,f305,f317,f339,f353,f375,f415,f424,f441,f486,f502,f514,f523,f532,f555,f625,f634,f873,f895,f930,f946,f1021,f1054,f1080,f1082,f1083,f1115,f1129,f1130])).

fof(f1130,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1129,plain,
    ( sK2 != k2_funct_1(sK3)
    | k1_relat_1(sK2) != k2_relat_1(k6_relat_1(sK0))
    | sK0 != k2_relat_1(k6_relat_1(sK0))
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1115,plain,
    ( spl4_88
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1110,f529,f479,f471,f182,f152,f1112])).

fof(f1112,plain,
    ( spl4_88
  <=> sK0 = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f152,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f182,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f471,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f479,plain,
    ( spl4_38
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f529,plain,
    ( spl4_44
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1110,plain,
    ( sK0 = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_38
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1109,f473])).

fof(f473,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f471])).

fof(f1109,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1108,f184])).

fof(f184,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1108,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_38
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1107,f154])).

fof(f154,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1107,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_38
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1086,f480])).

fof(f480,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f479])).

fof(f1086,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44 ),
    inference(superposition,[],[f80,f531])).

fof(f531,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f529])).

fof(f80,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f1083,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1082,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1080,plain,
    ( ~ spl4_83
    | spl4_84
    | ~ spl4_85
    | ~ spl4_86
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1063,f1018,f520,f483,f471,f182,f152,f1077,f1073,f1069,f1065])).

fof(f1065,plain,
    ( spl4_83
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f1069,plain,
    ( spl4_84
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1073,plain,
    ( spl4_85
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f1077,plain,
    ( spl4_86
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f483,plain,
    ( spl4_39
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f520,plain,
    ( spl4_43
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1018,plain,
    ( spl4_81
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1063,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_81 ),
    inference(forward_demodulation,[],[f1062,f473])).

fof(f1062,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_43
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f1061,f1020])).

fof(f1020,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f1061,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1060,f485])).

fof(f485,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f483])).

fof(f1060,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1059,f184])).

fof(f1059,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1028,f154])).

fof(f1028,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_43 ),
    inference(superposition,[],[f78,f522])).

fof(f522,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f520])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1054,plain,
    ( spl4_68
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_43
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f1053,f552,f520,f479,f182,f152,f943])).

fof(f943,plain,
    ( spl4_68
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f552,plain,
    ( spl4_46
  <=> sK1 = k1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1053,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_43
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f1052,f554])).

fof(f554,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f552])).

fof(f1052,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1051,f184])).

fof(f1051,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_38
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1050,f154])).

fof(f1050,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_38
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1025,f480])).

fof(f1025,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43 ),
    inference(superposition,[],[f81,f522])).

fof(f81,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
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
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f1021,plain,
    ( spl4_81
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1005,f499,f1018])).

fof(f499,plain,
    ( spl4_41
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1005,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_41 ),
    inference(resolution,[],[f501,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f501,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f499])).

fof(f946,plain,
    ( ~ spl4_38
    | spl4_67
    | ~ spl4_68
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f937,f631,f471,f216,f187,f182,f167,f152,f943,f939,f479])).

fof(f939,plain,
    ( spl4_67
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f167,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f187,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f216,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f631,plain,
    ( spl4_53
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f937,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f936,f218])).

fof(f218,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f216])).

fof(f936,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(trivial_inequality_removal,[],[f935])).

fof(f935,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f934,f473])).

fof(f934,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f933,f184])).

fof(f933,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f932,f154])).

fof(f932,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f931,f189])).

fof(f189,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f931,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f879,f169])).

fof(f169,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f879,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_53 ),
    inference(superposition,[],[f78,f633])).

fof(f633,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f631])).

fof(f930,plain,
    ( spl4_38
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_35
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f929,f622,f412,f167,f162,f157,f152,f147,f142,f137,f122,f479])).

fof(f122,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f137,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f142,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f147,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f157,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f162,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f412,plain,
    ( spl4_35
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f622,plain,
    ( spl4_51
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f929,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_35
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f928,f154])).

fof(f928,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_35
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f927,f149])).

fof(f149,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f927,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_35
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f926,f144])).

fof(f144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f926,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_35
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f913,f124])).

fof(f124,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f913,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_35
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f905,f414])).

fof(f414,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f412])).

fof(f905,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_51 ),
    inference(superposition,[],[f452,f624])).

fof(f624,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f622])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f451,f169])).

fof(f451,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f450,f164])).

fof(f164,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f450,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f449,f159])).

fof(f159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f449,plain,
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
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f446])).

fof(f446,plain,
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
    | ~ spl4_6 ),
    inference(superposition,[],[f93,f139])).

fof(f139,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f895,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_50 ),
    inference(avatar_contradiction_clause,[],[f894])).

fof(f894,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_50 ),
    inference(subsumption_resolution,[],[f893,f169])).

fof(f893,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_50 ),
    inference(subsumption_resolution,[],[f892,f159])).

fof(f892,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_50 ),
    inference(subsumption_resolution,[],[f891,f154])).

fof(f891,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_50 ),
    inference(subsumption_resolution,[],[f888,f144])).

fof(f888,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_50 ),
    inference(resolution,[],[f620,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f620,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl4_50
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f873,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_52 ),
    inference(avatar_contradiction_clause,[],[f871])).

fof(f871,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_52 ),
    inference(unit_resulting_resolution,[],[f169,f154,f159,f144,f629,f323])).

fof(f323,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f103,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f629,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl4_52
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f634,plain,
    ( ~ spl4_52
    | spl4_53
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f615,f314,f631,f627])).

fof(f314,plain,
    ( spl4_25
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f615,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_25 ),
    inference(resolution,[],[f245,f316])).

fof(f316,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f314])).

fof(f245,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f97,f177])).

fof(f177,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f100,f101])).

fof(f101,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f97,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f625,plain,
    ( ~ spl4_50
    | spl4_51
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f614,f173,f622,f618])).

fof(f173,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f614,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f245,f175])).

fof(f175,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f173])).

fof(f555,plain,
    ( spl4_46
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f550,f350,f216,f187,f167,f127,f552])).

fof(f127,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f350,plain,
    ( spl4_27
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f550,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f549,f218])).

fof(f549,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f548,f189])).

fof(f548,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f547,f169])).

fof(f547,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f534,f129])).

fof(f129,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f534,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_27 ),
    inference(superposition,[],[f79,f352])).

fof(f352,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f350])).

fof(f79,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f532,plain,
    ( spl4_44
    | ~ spl4_38
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f527,f438,f152,f147,f142,f122,f479,f529])).

fof(f438,plain,
    ( spl4_36
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f527,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f526,f154])).

fof(f526,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f525,f149])).

fof(f525,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f524,f144])).

fof(f524,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f462,f124])).

fof(f462,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f461])).

fof(f461,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f325,f440])).

fof(f440,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f438])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f74,f101])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f523,plain,
    ( spl4_43
    | ~ spl4_38
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f518,f438,f152,f147,f142,f122,f479,f520])).

fof(f518,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f517,f154])).

fof(f517,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f516,f149])).

fof(f516,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f515,f144])).

fof(f515,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f463,f124])).

fof(f463,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f460])).

fof(f460,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f324,f440])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f73,f101])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f514,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f513,f438,f142,f471])).

fof(f513,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f459,f144])).

fof(f459,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_36 ),
    inference(superposition,[],[f105,f440])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f502,plain,
    ( ~ spl4_38
    | spl4_41
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f497,f438,f152,f147,f142,f499,f479])).

fof(f497,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f496,f154])).

fof(f496,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f495,f149])).

fof(f495,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f466,f144])).

fof(f466,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f456])).

fof(f456,plain,
    ( sK0 != sK0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f77,f440])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f486,plain,
    ( ~ spl4_38
    | spl4_39
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f477,f438,f152,f147,f142,f483,f479])).

fof(f477,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f476,f154])).

fof(f476,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f475,f149])).

fof(f475,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f468,f144])).

fof(f468,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f454])).

fof(f454,plain,
    ( sK0 != sK0
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f75,f440])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f441,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f436,f173,f167,f162,f157,f152,f147,f142,f438])).

fof(f436,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f435,f154])).

fof(f435,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f434,f149])).

fof(f434,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f433,f144])).

fof(f433,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f432,f169])).

fof(f432,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f431,f164])).

fof(f431,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f428,f159])).

fof(f428,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f427,f175])).

fof(f427,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f99,f101])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f424,plain,
    ( ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_31 ),
    inference(subsumption_resolution,[],[f422,f189])).

fof(f422,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | spl4_31 ),
    inference(subsumption_resolution,[],[f421,f169])).

fof(f421,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | spl4_31 ),
    inference(subsumption_resolution,[],[f419,f129])).

fof(f419,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_31 ),
    inference(resolution,[],[f392,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f392,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl4_31
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f415,plain,
    ( ~ spl4_31
    | spl4_35
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f410,f336,f302,f256,f187,f167,f127,f412,f390])).

fof(f256,plain,
    ( spl4_19
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f302,plain,
    ( spl4_24
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f336,plain,
    ( spl4_26
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f410,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f409,f189])).

fof(f409,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f408,f169])).

fof(f408,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f407,f129])).

fof(f407,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f406,f304])).

fof(f304,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f302])).

fof(f406,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f358,f258])).

fof(f258,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f256])).

fof(f358,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f96,f338])).

fof(f338,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f336])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

fof(f375,plain,
    ( spl4_29
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f370,f336,f187,f167,f127,f372])).

fof(f372,plain,
    ( spl4_29
  <=> k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f370,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f369,f189])).

fof(f369,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f368,f169])).

fof(f368,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f355,f129])).

fof(f355,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f82,f338])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f353,plain,
    ( spl4_27
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f348,f167,f162,f157,f137,f127,f117,f350])).

fof(f117,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f348,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f347,f169])).

fof(f347,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f346,f164])).

fof(f346,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f345,f159])).

fof(f345,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f344,f129])).

fof(f344,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f343,f119])).

fof(f119,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f343,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f340])).

fof(f340,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f325,f139])).

fof(f339,plain,
    ( spl4_26
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f334,f167,f162,f157,f137,f127,f117,f336])).

fof(f334,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f333,f169])).

fof(f333,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f332,f164])).

fof(f332,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f331,f159])).

fof(f331,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f330,f129])).

fof(f330,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f329,f119])).

fof(f329,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f326])).

fof(f326,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f324,f139])).

fof(f317,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f312,f173,f167,f157,f152,f142,f314])).

fof(f312,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f311,f169])).

fof(f311,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f310,f159])).

fof(f310,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f309,f154])).

fof(f309,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f306,f144])).

fof(f306,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f175,f104])).

fof(f305,plain,
    ( spl4_24
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f289,f282,f302])).

fof(f282,plain,
    ( spl4_21
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f289,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(resolution,[],[f284,f106])).

fof(f284,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f282])).

fof(f295,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f290,f282,f142,f112,f292])).

fof(f292,plain,
    ( spl4_22
  <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f112,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f290,plain,
    ( ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | spl4_1
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f286,f114])).

fof(f114,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f286,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(resolution,[],[f284,f243])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | sK3 = X0
        | ~ r2_relset_1(sK1,sK0,X0,sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f97,f144])).

fof(f285,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f280,f167,f162,f157,f137,f127,f282])).

fof(f280,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f279,f169])).

fof(f279,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f278,f164])).

fof(f278,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f277,f159])).

fof(f277,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f276,f129])).

fof(f276,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f273])).

fof(f273,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f77,f139])).

fof(f259,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f254,f167,f162,f157,f137,f127,f256])).

fof(f254,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f253,f169])).

fof(f253,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f252,f164])).

fof(f252,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f251,f159])).

fof(f251,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f250,f129])).

fof(f250,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f247])).

fof(f247,plain,
    ( sK1 != sK1
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f75,f139])).

fof(f221,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f220,f157,f137,f216])).

fof(f220,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f213,f159])).

fof(f213,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f139,f105])).

fof(f201,plain,
    ( spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f194,f142,f198])).

fof(f198,plain,
    ( spl4_16
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f194,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f144])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f190,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f179,f157,f187])).

fof(f179,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f106,f159])).

fof(f185,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f178,f142,f182])).

fof(f178,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f106,f144])).

fof(f176,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f171,f132,f173])).

fof(f132,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f171,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f134,f101])).

fof(f134,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f170,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f61,f167])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f58,f57])).

fof(f57,plain,
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

fof(f58,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f165,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f62,f162])).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f160,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f63,f157])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f155,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f64,f152])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f150,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f65,f147])).

fof(f65,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f145,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f66,f142])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f140,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f67,f137])).

fof(f67,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f135,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f68,f132])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f130,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f69,f127])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f125,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f70,f122])).

fof(f70,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f71,f117])).

fof(f71,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f59])).

fof(f115,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f72,f112])).

fof(f72,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n025.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:13:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.51  % (14814)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.52  % (14830)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.52  % (14822)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.53  % (14809)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.53  % (14827)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.53  % (14819)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.54  % (14803)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (14804)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (14806)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.55  % (14805)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.55  % (14802)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.55  % (14828)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (14807)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (14816)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (14826)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.55  % (14824)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.56  % (14820)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.56  % (14825)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.56  % (14818)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.56  % (14818)Refutation not found, incomplete strategy% (14818)------------------------------
% 0.23/0.56  % (14818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (14818)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (14818)Memory used [KB]: 10746
% 0.23/0.56  % (14818)Time elapsed: 0.137 s
% 0.23/0.56  % (14818)------------------------------
% 0.23/0.56  % (14818)------------------------------
% 0.23/0.56  % (14808)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (14829)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.56  % (14815)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (14810)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.57  % (14811)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.57  % (14823)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.57  % (14821)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.57  % (14812)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.57  % (14813)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.57  % (14817)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.58  % (14831)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.99/0.63  % (14823)Refutation found. Thanks to Tanya!
% 1.99/0.63  % SZS status Theorem for theBenchmark
% 1.99/0.65  % SZS output start Proof for theBenchmark
% 1.99/0.65  fof(f1131,plain,(
% 1.99/0.65    $false),
% 1.99/0.65    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f176,f185,f190,f201,f221,f259,f285,f295,f305,f317,f339,f353,f375,f415,f424,f441,f486,f502,f514,f523,f532,f555,f625,f634,f873,f895,f930,f946,f1021,f1054,f1080,f1082,f1083,f1115,f1129,f1130])).
% 1.99/0.65  fof(f1130,plain,(
% 1.99/0.65    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | ~r2_relset_1(sK1,sK0,sK3,sK3)),
% 1.99/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.99/0.65  fof(f1129,plain,(
% 1.99/0.65    sK2 != k2_funct_1(sK3) | k1_relat_1(sK2) != k2_relat_1(k6_relat_1(sK0)) | sK0 != k2_relat_1(k6_relat_1(sK0)) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.99/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.99/0.65  fof(f1115,plain,(
% 1.99/0.65    spl4_88 | ~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_38 | ~spl4_44),
% 1.99/0.65    inference(avatar_split_clause,[],[f1110,f529,f479,f471,f182,f152,f1112])).
% 1.99/0.65  fof(f1112,plain,(
% 1.99/0.65    spl4_88 <=> sK0 = k2_relat_1(k6_relat_1(sK0))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 1.99/0.65  fof(f152,plain,(
% 1.99/0.65    spl4_9 <=> v1_funct_1(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.99/0.65  fof(f182,plain,(
% 1.99/0.65    spl4_14 <=> v1_relat_1(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.99/0.65  fof(f471,plain,(
% 1.99/0.65    spl4_37 <=> sK0 = k2_relat_1(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.99/0.65  fof(f479,plain,(
% 1.99/0.65    spl4_38 <=> v2_funct_1(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.99/0.65  fof(f529,plain,(
% 1.99/0.65    spl4_44 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.99/0.65  fof(f1110,plain,(
% 1.99/0.65    sK0 = k2_relat_1(k6_relat_1(sK0)) | (~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_38 | ~spl4_44)),
% 1.99/0.65    inference(forward_demodulation,[],[f1109,f473])).
% 1.99/0.65  fof(f473,plain,(
% 1.99/0.65    sK0 = k2_relat_1(sK3) | ~spl4_37),
% 1.99/0.65    inference(avatar_component_clause,[],[f471])).
% 1.99/0.65  fof(f1109,plain,(
% 1.99/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_44)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1108,f184])).
% 1.99/0.65  fof(f184,plain,(
% 1.99/0.65    v1_relat_1(sK3) | ~spl4_14),
% 1.99/0.65    inference(avatar_component_clause,[],[f182])).
% 1.99/0.65  fof(f1108,plain,(
% 1.99/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_38 | ~spl4_44)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1107,f154])).
% 1.99/0.65  fof(f154,plain,(
% 1.99/0.65    v1_funct_1(sK3) | ~spl4_9),
% 1.99/0.65    inference(avatar_component_clause,[],[f152])).
% 1.99/0.65  fof(f1107,plain,(
% 1.99/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_38 | ~spl4_44)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1086,f480])).
% 1.99/0.65  fof(f480,plain,(
% 1.99/0.65    v2_funct_1(sK3) | ~spl4_38),
% 1.99/0.65    inference(avatar_component_clause,[],[f479])).
% 1.99/0.65  fof(f1086,plain,(
% 1.99/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_44),
% 1.99/0.65    inference(superposition,[],[f80,f531])).
% 1.99/0.65  fof(f531,plain,(
% 1.99/0.65    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_44),
% 1.99/0.65    inference(avatar_component_clause,[],[f529])).
% 1.99/0.65  fof(f80,plain,(
% 1.99/0.65    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f32])).
% 1.99/0.65  fof(f32,plain,(
% 1.99/0.65    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.65    inference(flattening,[],[f31])).
% 1.99/0.65  fof(f31,plain,(
% 1.99/0.65    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.99/0.65    inference(ennf_transformation,[],[f6])).
% 1.99/0.65  fof(f6,axiom,(
% 1.99/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.99/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.99/0.65  fof(f1083,plain,(
% 1.99/0.65    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.99/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.99/0.65  fof(f1082,plain,(
% 1.99/0.65    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.99/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.99/0.65  fof(f1080,plain,(
% 1.99/0.65    ~spl4_83 | spl4_84 | ~spl4_85 | ~spl4_86 | ~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_39 | ~spl4_43 | ~spl4_81),
% 1.99/0.65    inference(avatar_split_clause,[],[f1063,f1018,f520,f483,f471,f182,f152,f1077,f1073,f1069,f1065])).
% 1.99/0.65  fof(f1065,plain,(
% 1.99/0.65    spl4_83 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 1.99/0.65  fof(f1069,plain,(
% 1.99/0.65    spl4_84 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 1.99/0.65  fof(f1073,plain,(
% 1.99/0.65    spl4_85 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 1.99/0.65  fof(f1077,plain,(
% 1.99/0.65    spl4_86 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 1.99/0.65  fof(f483,plain,(
% 1.99/0.65    spl4_39 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.99/0.65  fof(f520,plain,(
% 1.99/0.65    spl4_43 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.99/0.65  fof(f1018,plain,(
% 1.99/0.65    spl4_81 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 1.99/0.65  fof(f1063,plain,(
% 1.99/0.65    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_39 | ~spl4_43 | ~spl4_81)),
% 1.99/0.65    inference(forward_demodulation,[],[f1062,f473])).
% 1.99/0.65  fof(f1062,plain,(
% 1.99/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_43 | ~spl4_81)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1061,f1020])).
% 1.99/0.65  fof(f1020,plain,(
% 1.99/0.65    v1_relat_1(k2_funct_1(sK3)) | ~spl4_81),
% 1.99/0.65    inference(avatar_component_clause,[],[f1018])).
% 1.99/0.65  fof(f1061,plain,(
% 1.99/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_39 | ~spl4_43)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1060,f485])).
% 1.99/0.65  fof(f485,plain,(
% 1.99/0.65    v1_funct_1(k2_funct_1(sK3)) | ~spl4_39),
% 1.99/0.65    inference(avatar_component_clause,[],[f483])).
% 1.99/0.65  fof(f1060,plain,(
% 1.99/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_43)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1059,f184])).
% 1.99/0.65  fof(f1059,plain,(
% 1.99/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_43)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1028,f154])).
% 1.99/0.65  fof(f1028,plain,(
% 1.99/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_43),
% 1.99/0.65    inference(superposition,[],[f78,f522])).
% 1.99/0.65  fof(f522,plain,(
% 1.99/0.65    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_43),
% 1.99/0.65    inference(avatar_component_clause,[],[f520])).
% 1.99/0.65  fof(f78,plain,(
% 1.99/0.65    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f30])).
% 1.99/0.65  fof(f30,plain,(
% 1.99/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.65    inference(flattening,[],[f29])).
% 1.99/0.65  fof(f29,plain,(
% 1.99/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.99/0.65    inference(ennf_transformation,[],[f7])).
% 1.99/0.65  fof(f7,axiom,(
% 1.99/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.99/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.99/0.65  fof(f1054,plain,(
% 1.99/0.65    spl4_68 | ~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_43 | ~spl4_46),
% 1.99/0.65    inference(avatar_split_clause,[],[f1053,f552,f520,f479,f182,f152,f943])).
% 1.99/0.65  fof(f943,plain,(
% 1.99/0.65    spl4_68 <=> sK1 = k1_relat_1(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.99/0.65  fof(f552,plain,(
% 1.99/0.65    spl4_46 <=> sK1 = k1_relat_1(k6_relat_1(sK1))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.99/0.65  fof(f1053,plain,(
% 1.99/0.65    sK1 = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_43 | ~spl4_46)),
% 1.99/0.65    inference(forward_demodulation,[],[f1052,f554])).
% 1.99/0.65  fof(f554,plain,(
% 1.99/0.65    sK1 = k1_relat_1(k6_relat_1(sK1)) | ~spl4_46),
% 1.99/0.65    inference(avatar_component_clause,[],[f552])).
% 1.99/0.65  fof(f1052,plain,(
% 1.99/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_43)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1051,f184])).
% 1.99/0.65  fof(f1051,plain,(
% 1.99/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_38 | ~spl4_43)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1050,f154])).
% 1.99/0.65  fof(f1050,plain,(
% 1.99/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_38 | ~spl4_43)),
% 1.99/0.65    inference(subsumption_resolution,[],[f1025,f480])).
% 1.99/0.65  fof(f1025,plain,(
% 1.99/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_43),
% 1.99/0.65    inference(superposition,[],[f81,f522])).
% 1.99/0.65  fof(f81,plain,(
% 1.99/0.65    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f34])).
% 1.99/0.65  fof(f34,plain,(
% 1.99/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.65    inference(flattening,[],[f33])).
% 1.99/0.65  fof(f33,plain,(
% 1.99/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.99/0.65    inference(ennf_transformation,[],[f5])).
% 1.99/0.65  fof(f5,axiom,(
% 1.99/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.99/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 1.99/0.65  fof(f1021,plain,(
% 1.99/0.65    spl4_81 | ~spl4_41),
% 1.99/0.65    inference(avatar_split_clause,[],[f1005,f499,f1018])).
% 1.99/0.65  fof(f499,plain,(
% 1.99/0.65    spl4_41 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.99/0.65  fof(f1005,plain,(
% 1.99/0.65    v1_relat_1(k2_funct_1(sK3)) | ~spl4_41),
% 1.99/0.65    inference(resolution,[],[f501,f106])).
% 1.99/0.65  fof(f106,plain,(
% 1.99/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.99/0.65    inference(cnf_transformation,[],[f56])).
% 1.99/0.65  fof(f56,plain,(
% 1.99/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.65    inference(ennf_transformation,[],[f9])).
% 1.99/0.65  fof(f9,axiom,(
% 1.99/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.99/0.65  fof(f501,plain,(
% 1.99/0.65    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_41),
% 1.99/0.65    inference(avatar_component_clause,[],[f499])).
% 1.99/0.65  fof(f946,plain,(
% 1.99/0.65    ~spl4_38 | spl4_67 | ~spl4_68 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_53),
% 1.99/0.65    inference(avatar_split_clause,[],[f937,f631,f471,f216,f187,f182,f167,f152,f943,f939,f479])).
% 1.99/0.65  fof(f939,plain,(
% 1.99/0.65    spl4_67 <=> sK2 = k2_funct_1(sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.99/0.65  fof(f167,plain,(
% 1.99/0.65    spl4_12 <=> v1_funct_1(sK2)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.99/0.65  fof(f187,plain,(
% 1.99/0.65    spl4_15 <=> v1_relat_1(sK2)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.99/0.65  fof(f216,plain,(
% 1.99/0.65    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.99/0.65  fof(f631,plain,(
% 1.99/0.65    spl4_53 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.99/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.99/0.65  fof(f937,plain,(
% 1.99/0.65    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_53)),
% 1.99/0.65    inference(forward_demodulation,[],[f936,f218])).
% 1.99/0.65  fof(f218,plain,(
% 1.99/0.65    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.99/0.65    inference(avatar_component_clause,[],[f216])).
% 1.99/0.65  fof(f936,plain,(
% 1.99/0.65    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_53)),
% 1.99/0.65    inference(trivial_inequality_removal,[],[f935])).
% 1.99/0.65  fof(f935,plain,(
% 1.99/0.65    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_53)),
% 1.99/0.65    inference(forward_demodulation,[],[f934,f473])).
% 1.99/0.65  fof(f934,plain,(
% 1.99/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_53)),
% 1.99/0.65    inference(subsumption_resolution,[],[f933,f184])).
% 1.99/0.65  fof(f933,plain,(
% 1.99/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_53)),
% 1.99/0.65    inference(subsumption_resolution,[],[f932,f154])).
% 1.99/0.65  fof(f932,plain,(
% 1.99/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_53)),
% 1.99/0.65    inference(subsumption_resolution,[],[f931,f189])).
% 1.99/0.65  fof(f189,plain,(
% 1.99/0.65    v1_relat_1(sK2) | ~spl4_15),
% 1.99/0.65    inference(avatar_component_clause,[],[f187])).
% 1.99/0.65  fof(f931,plain,(
% 1.99/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_53)),
% 1.99/0.65    inference(subsumption_resolution,[],[f879,f169])).
% 1.99/0.65  fof(f169,plain,(
% 1.99/0.65    v1_funct_1(sK2) | ~spl4_12),
% 1.99/0.65    inference(avatar_component_clause,[],[f167])).
% 1.99/0.65  fof(f879,plain,(
% 1.99/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_53),
% 1.99/0.65    inference(superposition,[],[f78,f633])).
% 1.99/0.65  fof(f633,plain,(
% 1.99/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_53),
% 1.99/0.65    inference(avatar_component_clause,[],[f631])).
% 1.99/0.66  fof(f930,plain,(
% 1.99/0.66    spl4_38 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_35 | ~spl4_51),
% 1.99/0.66    inference(avatar_split_clause,[],[f929,f622,f412,f167,f162,f157,f152,f147,f142,f137,f122,f479])).
% 1.99/0.66  fof(f122,plain,(
% 1.99/0.66    spl4_3 <=> k1_xboole_0 = sK0),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.99/0.66  fof(f137,plain,(
% 1.99/0.66    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.99/0.66  fof(f142,plain,(
% 1.99/0.66    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.99/0.66  fof(f147,plain,(
% 1.99/0.66    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.99/0.66  fof(f157,plain,(
% 1.99/0.66    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.99/0.66  fof(f162,plain,(
% 1.99/0.66    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.99/0.66  fof(f412,plain,(
% 1.99/0.66    spl4_35 <=> v2_funct_1(k6_relat_1(sK0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.99/0.66  fof(f622,plain,(
% 1.99/0.66    spl4_51 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.99/0.66  fof(f929,plain,(
% 1.99/0.66    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_35 | ~spl4_51)),
% 1.99/0.66    inference(subsumption_resolution,[],[f928,f154])).
% 1.99/0.66  fof(f928,plain,(
% 1.99/0.66    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_35 | ~spl4_51)),
% 1.99/0.66    inference(subsumption_resolution,[],[f927,f149])).
% 1.99/0.66  fof(f149,plain,(
% 1.99/0.66    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.99/0.66    inference(avatar_component_clause,[],[f147])).
% 1.99/0.66  fof(f927,plain,(
% 1.99/0.66    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_35 | ~spl4_51)),
% 1.99/0.66    inference(subsumption_resolution,[],[f926,f144])).
% 1.99/0.66  fof(f144,plain,(
% 1.99/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.99/0.66    inference(avatar_component_clause,[],[f142])).
% 1.99/0.66  fof(f926,plain,(
% 1.99/0.66    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_35 | ~spl4_51)),
% 1.99/0.66    inference(subsumption_resolution,[],[f913,f124])).
% 1.99/0.66  fof(f124,plain,(
% 1.99/0.66    k1_xboole_0 != sK0 | spl4_3),
% 1.99/0.66    inference(avatar_component_clause,[],[f122])).
% 1.99/0.66  fof(f913,plain,(
% 1.99/0.66    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_35 | ~spl4_51)),
% 1.99/0.66    inference(subsumption_resolution,[],[f905,f414])).
% 1.99/0.66  fof(f414,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~spl4_35),
% 1.99/0.66    inference(avatar_component_clause,[],[f412])).
% 1.99/0.66  fof(f905,plain,(
% 1.99/0.66    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_51)),
% 1.99/0.66    inference(superposition,[],[f452,f624])).
% 1.99/0.66  fof(f624,plain,(
% 1.99/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_51),
% 1.99/0.66    inference(avatar_component_clause,[],[f622])).
% 1.99/0.66  fof(f452,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.99/0.66    inference(subsumption_resolution,[],[f451,f169])).
% 1.99/0.66  fof(f451,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.99/0.66    inference(subsumption_resolution,[],[f450,f164])).
% 1.99/0.66  fof(f164,plain,(
% 1.99/0.66    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.99/0.66    inference(avatar_component_clause,[],[f162])).
% 1.99/0.66  fof(f450,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.99/0.66    inference(subsumption_resolution,[],[f449,f159])).
% 1.99/0.66  fof(f159,plain,(
% 1.99/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.99/0.66    inference(avatar_component_clause,[],[f157])).
% 1.99/0.66  fof(f449,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f446])).
% 1.99/0.66  fof(f446,plain,(
% 1.99/0.66    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.99/0.66    inference(superposition,[],[f93,f139])).
% 1.99/0.66  fof(f139,plain,(
% 1.99/0.66    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.99/0.66    inference(avatar_component_clause,[],[f137])).
% 1.99/0.66  fof(f93,plain,(
% 1.99/0.66    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f44])).
% 1.99/0.66  fof(f44,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.99/0.66    inference(flattening,[],[f43])).
% 1.99/0.66  fof(f43,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.99/0.66    inference(ennf_transformation,[],[f17])).
% 1.99/0.66  fof(f17,axiom,(
% 1.99/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.99/0.66  fof(f895,plain,(
% 1.99/0.66    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_50),
% 1.99/0.66    inference(avatar_contradiction_clause,[],[f894])).
% 1.99/0.66  fof(f894,plain,(
% 1.99/0.66    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_50)),
% 1.99/0.66    inference(subsumption_resolution,[],[f893,f169])).
% 1.99/0.66  fof(f893,plain,(
% 1.99/0.66    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_50)),
% 1.99/0.66    inference(subsumption_resolution,[],[f892,f159])).
% 1.99/0.66  fof(f892,plain,(
% 1.99/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_50)),
% 1.99/0.66    inference(subsumption_resolution,[],[f891,f154])).
% 1.99/0.66  fof(f891,plain,(
% 1.99/0.66    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_50)),
% 1.99/0.66    inference(subsumption_resolution,[],[f888,f144])).
% 1.99/0.66  fof(f888,plain,(
% 1.99/0.66    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_50),
% 1.99/0.66    inference(resolution,[],[f620,f103])).
% 1.99/0.66  fof(f103,plain,(
% 1.99/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f52])).
% 1.99/0.66  fof(f52,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.99/0.66    inference(flattening,[],[f51])).
% 1.99/0.66  fof(f51,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.99/0.66    inference(ennf_transformation,[],[f12])).
% 1.99/0.66  fof(f12,axiom,(
% 1.99/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.99/0.66  fof(f620,plain,(
% 1.99/0.66    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_50),
% 1.99/0.66    inference(avatar_component_clause,[],[f618])).
% 1.99/0.66  fof(f618,plain,(
% 1.99/0.66    spl4_50 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.99/0.66  fof(f873,plain,(
% 1.99/0.66    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_52),
% 1.99/0.66    inference(avatar_contradiction_clause,[],[f871])).
% 1.99/0.66  fof(f871,plain,(
% 1.99/0.66    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_52)),
% 1.99/0.66    inference(unit_resulting_resolution,[],[f169,f154,f159,f144,f629,f323])).
% 1.99/0.66  fof(f323,plain,(
% 1.99/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.99/0.66    inference(duplicate_literal_removal,[],[f322])).
% 1.99/0.66  fof(f322,plain,(
% 1.99/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.99/0.66    inference(superposition,[],[f103,f104])).
% 1.99/0.66  fof(f104,plain,(
% 1.99/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f54])).
% 1.99/0.66  fof(f54,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.99/0.66    inference(flattening,[],[f53])).
% 1.99/0.66  fof(f53,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.99/0.66    inference(ennf_transformation,[],[f14])).
% 1.99/0.66  fof(f14,axiom,(
% 1.99/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.99/0.66  fof(f629,plain,(
% 1.99/0.66    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_52),
% 1.99/0.66    inference(avatar_component_clause,[],[f627])).
% 1.99/0.66  fof(f627,plain,(
% 1.99/0.66    spl4_52 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.99/0.66  fof(f634,plain,(
% 1.99/0.66    ~spl4_52 | spl4_53 | ~spl4_25),
% 1.99/0.66    inference(avatar_split_clause,[],[f615,f314,f631,f627])).
% 1.99/0.66  fof(f314,plain,(
% 1.99/0.66    spl4_25 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.99/0.66  fof(f615,plain,(
% 1.99/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_25),
% 1.99/0.66    inference(resolution,[],[f245,f316])).
% 1.99/0.66  fof(f316,plain,(
% 1.99/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_25),
% 1.99/0.66    inference(avatar_component_clause,[],[f314])).
% 1.99/0.66  fof(f245,plain,(
% 1.99/0.66    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.99/0.66    inference(resolution,[],[f97,f177])).
% 1.99/0.66  fof(f177,plain,(
% 1.99/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f100,f101])).
% 1.99/0.66  fof(f101,plain,(
% 1.99/0.66    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f15])).
% 1.99/0.66  fof(f15,axiom,(
% 1.99/0.66    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.99/0.66  fof(f100,plain,(
% 1.99/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f22])).
% 1.99/0.66  fof(f22,plain,(
% 1.99/0.66    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.99/0.66    inference(pure_predicate_removal,[],[f13])).
% 1.99/0.66  fof(f13,axiom,(
% 1.99/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.99/0.66  fof(f97,plain,(
% 1.99/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f60])).
% 1.99/0.66  fof(f60,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.66    inference(nnf_transformation,[],[f48])).
% 1.99/0.66  fof(f48,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.66    inference(flattening,[],[f47])).
% 1.99/0.66  fof(f47,plain,(
% 1.99/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.99/0.66    inference(ennf_transformation,[],[f11])).
% 1.99/0.66  fof(f11,axiom,(
% 1.99/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.99/0.66  fof(f625,plain,(
% 1.99/0.66    ~spl4_50 | spl4_51 | ~spl4_13),
% 1.99/0.66    inference(avatar_split_clause,[],[f614,f173,f622,f618])).
% 1.99/0.66  fof(f173,plain,(
% 1.99/0.66    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.99/0.66  fof(f614,plain,(
% 1.99/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.99/0.66    inference(resolution,[],[f245,f175])).
% 1.99/0.66  fof(f175,plain,(
% 1.99/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.99/0.66    inference(avatar_component_clause,[],[f173])).
% 1.99/0.66  fof(f555,plain,(
% 1.99/0.66    spl4_46 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_27),
% 1.99/0.66    inference(avatar_split_clause,[],[f550,f350,f216,f187,f167,f127,f552])).
% 1.99/0.66  fof(f127,plain,(
% 1.99/0.66    spl4_4 <=> v2_funct_1(sK2)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.99/0.66  fof(f350,plain,(
% 1.99/0.66    spl4_27 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.99/0.66  fof(f550,plain,(
% 1.99/0.66    sK1 = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_27)),
% 1.99/0.66    inference(forward_demodulation,[],[f549,f218])).
% 1.99/0.66  fof(f549,plain,(
% 1.99/0.66    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27)),
% 1.99/0.66    inference(subsumption_resolution,[],[f548,f189])).
% 1.99/0.66  fof(f548,plain,(
% 1.99/0.66    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_27)),
% 1.99/0.66    inference(subsumption_resolution,[],[f547,f169])).
% 1.99/0.66  fof(f547,plain,(
% 1.99/0.66    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_27)),
% 1.99/0.66    inference(subsumption_resolution,[],[f534,f129])).
% 1.99/0.66  fof(f129,plain,(
% 1.99/0.66    v2_funct_1(sK2) | ~spl4_4),
% 1.99/0.66    inference(avatar_component_clause,[],[f127])).
% 1.99/0.66  fof(f534,plain,(
% 1.99/0.66    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_27),
% 1.99/0.66    inference(superposition,[],[f79,f352])).
% 1.99/0.66  fof(f352,plain,(
% 1.99/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_27),
% 1.99/0.66    inference(avatar_component_clause,[],[f350])).
% 1.99/0.66  fof(f79,plain,(
% 1.99/0.66    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f32])).
% 1.99/0.66  fof(f532,plain,(
% 1.99/0.66    spl4_44 | ~spl4_38 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 1.99/0.66    inference(avatar_split_clause,[],[f527,f438,f152,f147,f142,f122,f479,f529])).
% 1.99/0.66  fof(f438,plain,(
% 1.99/0.66    spl4_36 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.99/0.66  fof(f527,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f526,f154])).
% 1.99/0.66  fof(f526,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f525,f149])).
% 1.99/0.66  fof(f525,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f524,f144])).
% 1.99/0.66  fof(f524,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f462,f124])).
% 1.99/0.66  fof(f462,plain,(
% 1.99/0.66    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f461])).
% 1.99/0.66  fof(f461,plain,(
% 1.99/0.66    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(superposition,[],[f325,f440])).
% 1.99/0.66  fof(f440,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_36),
% 1.99/0.66    inference(avatar_component_clause,[],[f438])).
% 1.99/0.66  fof(f325,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(forward_demodulation,[],[f74,f101])).
% 1.99/0.66  fof(f74,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f26])).
% 1.99/0.66  fof(f26,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.99/0.66    inference(flattening,[],[f25])).
% 1.99/0.66  fof(f25,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.99/0.66    inference(ennf_transformation,[],[f19])).
% 1.99/0.66  fof(f19,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.99/0.66  fof(f523,plain,(
% 1.99/0.66    spl4_43 | ~spl4_38 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 1.99/0.66    inference(avatar_split_clause,[],[f518,f438,f152,f147,f142,f122,f479,f520])).
% 1.99/0.66  fof(f518,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f517,f154])).
% 1.99/0.66  fof(f517,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f516,f149])).
% 1.99/0.66  fof(f516,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f515,f144])).
% 1.99/0.66  fof(f515,plain,(
% 1.99/0.66    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f463,f124])).
% 1.99/0.66  fof(f463,plain,(
% 1.99/0.66    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f460])).
% 1.99/0.66  fof(f460,plain,(
% 1.99/0.66    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(superposition,[],[f324,f440])).
% 1.99/0.66  fof(f324,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(forward_demodulation,[],[f73,f101])).
% 1.99/0.66  fof(f73,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f26])).
% 1.99/0.66  fof(f514,plain,(
% 1.99/0.66    spl4_37 | ~spl4_7 | ~spl4_36),
% 1.99/0.66    inference(avatar_split_clause,[],[f513,f438,f142,f471])).
% 1.99/0.66  fof(f513,plain,(
% 1.99/0.66    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f459,f144])).
% 1.99/0.66  fof(f459,plain,(
% 1.99/0.66    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_36),
% 1.99/0.66    inference(superposition,[],[f105,f440])).
% 1.99/0.66  fof(f105,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f55])).
% 1.99/0.66  fof(f55,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.66    inference(ennf_transformation,[],[f10])).
% 1.99/0.66  fof(f10,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.99/0.66  fof(f502,plain,(
% 1.99/0.66    ~spl4_38 | spl4_41 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 1.99/0.66    inference(avatar_split_clause,[],[f497,f438,f152,f147,f142,f499,f479])).
% 1.99/0.66  fof(f497,plain,(
% 1.99/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f496,f154])).
% 1.99/0.66  fof(f496,plain,(
% 1.99/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f495,f149])).
% 1.99/0.66  fof(f495,plain,(
% 1.99/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f466,f144])).
% 1.99/0.66  fof(f466,plain,(
% 1.99/0.66    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f456])).
% 1.99/0.66  fof(f456,plain,(
% 1.99/0.66    sK0 != sK0 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(superposition,[],[f77,f440])).
% 1.99/0.66  fof(f77,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f28])).
% 1.99/0.66  fof(f28,plain,(
% 1.99/0.66    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.99/0.66    inference(flattening,[],[f27])).
% 1.99/0.66  fof(f27,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.99/0.66    inference(ennf_transformation,[],[f18])).
% 1.99/0.66  fof(f18,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.99/0.66  fof(f486,plain,(
% 1.99/0.66    ~spl4_38 | spl4_39 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 1.99/0.66    inference(avatar_split_clause,[],[f477,f438,f152,f147,f142,f483,f479])).
% 1.99/0.66  fof(f477,plain,(
% 1.99/0.66    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f476,f154])).
% 1.99/0.66  fof(f476,plain,(
% 1.99/0.66    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f475,f149])).
% 1.99/0.66  fof(f475,plain,(
% 1.99/0.66    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_36)),
% 1.99/0.66    inference(subsumption_resolution,[],[f468,f144])).
% 1.99/0.66  fof(f468,plain,(
% 1.99/0.66    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f454])).
% 1.99/0.66  fof(f454,plain,(
% 1.99/0.66    sK0 != sK0 | v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 1.99/0.66    inference(superposition,[],[f75,f440])).
% 1.99/0.66  fof(f75,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f28])).
% 1.99/0.66  fof(f441,plain,(
% 1.99/0.66    spl4_36 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.99/0.66    inference(avatar_split_clause,[],[f436,f173,f167,f162,f157,f152,f147,f142,f438])).
% 1.99/0.66  fof(f436,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f435,f154])).
% 1.99/0.66  fof(f435,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f434,f149])).
% 1.99/0.66  fof(f434,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f433,f144])).
% 1.99/0.66  fof(f433,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f432,f169])).
% 1.99/0.66  fof(f432,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f431,f164])).
% 1.99/0.66  fof(f431,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f428,f159])).
% 1.99/0.66  fof(f428,plain,(
% 1.99/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.99/0.66    inference(resolution,[],[f427,f175])).
% 1.99/0.66  fof(f427,plain,(
% 1.99/0.66    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(forward_demodulation,[],[f99,f101])).
% 1.99/0.66  fof(f99,plain,(
% 1.99/0.66    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f50])).
% 1.99/0.66  fof(f50,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.99/0.66    inference(flattening,[],[f49])).
% 1.99/0.66  fof(f49,plain,(
% 1.99/0.66    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.99/0.66    inference(ennf_transformation,[],[f16])).
% 1.99/0.66  fof(f16,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.99/0.66  fof(f424,plain,(
% 1.99/0.66    ~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_31),
% 1.99/0.66    inference(avatar_contradiction_clause,[],[f423])).
% 1.99/0.66  fof(f423,plain,(
% 1.99/0.66    $false | (~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_31)),
% 1.99/0.66    inference(subsumption_resolution,[],[f422,f189])).
% 1.99/0.66  fof(f422,plain,(
% 1.99/0.66    ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | spl4_31)),
% 1.99/0.66    inference(subsumption_resolution,[],[f421,f169])).
% 1.99/0.66  fof(f421,plain,(
% 1.99/0.66    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | spl4_31)),
% 1.99/0.66    inference(subsumption_resolution,[],[f419,f129])).
% 1.99/0.66  fof(f419,plain,(
% 1.99/0.66    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_31),
% 1.99/0.66    inference(resolution,[],[f392,f90])).
% 1.99/0.66  fof(f90,plain,(
% 1.99/0.66    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f42])).
% 1.99/0.66  fof(f42,plain,(
% 1.99/0.66    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.66    inference(flattening,[],[f41])).
% 1.99/0.66  fof(f41,plain,(
% 1.99/0.66    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f2])).
% 1.99/0.66  fof(f2,axiom,(
% 1.99/0.66    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.99/0.66  fof(f392,plain,(
% 1.99/0.66    ~v2_funct_1(k2_funct_1(sK2)) | spl4_31),
% 1.99/0.66    inference(avatar_component_clause,[],[f390])).
% 1.99/0.66  fof(f390,plain,(
% 1.99/0.66    spl4_31 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.99/0.66  fof(f415,plain,(
% 1.99/0.66    ~spl4_31 | spl4_35 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19 | ~spl4_24 | ~spl4_26),
% 1.99/0.66    inference(avatar_split_clause,[],[f410,f336,f302,f256,f187,f167,f127,f412,f390])).
% 1.99/0.66  fof(f256,plain,(
% 1.99/0.66    spl4_19 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.99/0.66  fof(f302,plain,(
% 1.99/0.66    spl4_24 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.99/0.66  fof(f336,plain,(
% 1.99/0.66    spl4_26 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.99/0.66  fof(f410,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f409,f189])).
% 1.99/0.66  fof(f409,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f408,f169])).
% 1.99/0.66  fof(f408,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f407,f129])).
% 1.99/0.66  fof(f407,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f406,f304])).
% 1.99/0.66  fof(f304,plain,(
% 1.99/0.66    v1_relat_1(k2_funct_1(sK2)) | ~spl4_24),
% 1.99/0.66    inference(avatar_component_clause,[],[f302])).
% 1.99/0.66  fof(f406,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_19 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f358,f258])).
% 1.99/0.66  fof(f258,plain,(
% 1.99/0.66    v1_funct_1(k2_funct_1(sK2)) | ~spl4_19),
% 1.99/0.66    inference(avatar_component_clause,[],[f256])).
% 1.99/0.66  fof(f358,plain,(
% 1.99/0.66    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_26),
% 1.99/0.66    inference(superposition,[],[f96,f338])).
% 1.99/0.66  fof(f338,plain,(
% 1.99/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_26),
% 1.99/0.66    inference(avatar_component_clause,[],[f336])).
% 1.99/0.66  fof(f96,plain,(
% 1.99/0.66    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f46])).
% 1.99/0.66  fof(f46,plain,(
% 1.99/0.66    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.99/0.66    inference(flattening,[],[f45])).
% 1.99/0.66  fof(f45,plain,(
% 1.99/0.66    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f3])).
% 1.99/0.66  fof(f3,axiom,(
% 1.99/0.66    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).
% 1.99/0.66  fof(f375,plain,(
% 1.99/0.66    spl4_29 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26),
% 1.99/0.66    inference(avatar_split_clause,[],[f370,f336,f187,f167,f127,f372])).
% 1.99/0.66  fof(f372,plain,(
% 1.99/0.66    spl4_29 <=> k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.99/0.66  fof(f370,plain,(
% 1.99/0.66    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f369,f189])).
% 1.99/0.66  fof(f369,plain,(
% 1.99/0.66    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f368,f169])).
% 1.99/0.66  fof(f368,plain,(
% 1.99/0.66    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_26)),
% 1.99/0.66    inference(subsumption_resolution,[],[f355,f129])).
% 1.99/0.66  fof(f355,plain,(
% 1.99/0.66    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_26),
% 1.99/0.66    inference(superposition,[],[f82,f338])).
% 1.99/0.66  fof(f82,plain,(
% 1.99/0.66    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f34])).
% 1.99/0.66  fof(f353,plain,(
% 1.99/0.66    spl4_27 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.99/0.66    inference(avatar_split_clause,[],[f348,f167,f162,f157,f137,f127,f117,f350])).
% 1.99/0.66  fof(f117,plain,(
% 1.99/0.66    spl4_2 <=> k1_xboole_0 = sK1),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.99/0.66  fof(f348,plain,(
% 1.99/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.99/0.66    inference(subsumption_resolution,[],[f347,f169])).
% 1.99/0.66  fof(f347,plain,(
% 1.99/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.99/0.66    inference(subsumption_resolution,[],[f346,f164])).
% 1.99/0.66  fof(f346,plain,(
% 1.99/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.99/0.66    inference(subsumption_resolution,[],[f345,f159])).
% 1.99/0.66  fof(f345,plain,(
% 1.99/0.66    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.99/0.66    inference(subsumption_resolution,[],[f344,f129])).
% 1.99/0.66  fof(f344,plain,(
% 1.99/0.66    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.99/0.66    inference(subsumption_resolution,[],[f343,f119])).
% 1.99/0.66  fof(f119,plain,(
% 1.99/0.66    k1_xboole_0 != sK1 | spl4_2),
% 1.99/0.66    inference(avatar_component_clause,[],[f117])).
% 1.99/0.66  fof(f343,plain,(
% 1.99/0.66    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f340])).
% 1.99/0.66  fof(f340,plain,(
% 1.99/0.66    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.66    inference(superposition,[],[f325,f139])).
% 1.99/0.66  fof(f339,plain,(
% 1.99/0.66    spl4_26 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.99/0.66    inference(avatar_split_clause,[],[f334,f167,f162,f157,f137,f127,f117,f336])).
% 1.99/0.66  fof(f334,plain,(
% 1.99/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.99/0.66    inference(subsumption_resolution,[],[f333,f169])).
% 1.99/0.66  fof(f333,plain,(
% 1.99/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.99/0.66    inference(subsumption_resolution,[],[f332,f164])).
% 1.99/0.66  fof(f332,plain,(
% 1.99/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.99/0.66    inference(subsumption_resolution,[],[f331,f159])).
% 1.99/0.66  fof(f331,plain,(
% 1.99/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.99/0.66    inference(subsumption_resolution,[],[f330,f129])).
% 1.99/0.66  fof(f330,plain,(
% 1.99/0.66    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.99/0.66    inference(subsumption_resolution,[],[f329,f119])).
% 1.99/0.66  fof(f329,plain,(
% 1.99/0.66    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.66    inference(trivial_inequality_removal,[],[f326])).
% 1.99/0.66  fof(f326,plain,(
% 1.99/0.66    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.66    inference(superposition,[],[f324,f139])).
% 1.99/0.66  fof(f317,plain,(
% 1.99/0.66    spl4_25 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.99/0.66    inference(avatar_split_clause,[],[f312,f173,f167,f157,f152,f142,f314])).
% 1.99/0.66  fof(f312,plain,(
% 1.99/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f311,f169])).
% 1.99/0.66  fof(f311,plain,(
% 1.99/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f310,f159])).
% 1.99/0.66  fof(f310,plain,(
% 1.99/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.99/0.66    inference(subsumption_resolution,[],[f309,f154])).
% 1.99/0.67  fof(f309,plain,(
% 1.99/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.99/0.67    inference(subsumption_resolution,[],[f306,f144])).
% 1.99/0.67  fof(f306,plain,(
% 1.99/0.67    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.99/0.67    inference(superposition,[],[f175,f104])).
% 1.99/0.67  fof(f305,plain,(
% 1.99/0.67    spl4_24 | ~spl4_21),
% 1.99/0.67    inference(avatar_split_clause,[],[f289,f282,f302])).
% 1.99/0.67  fof(f282,plain,(
% 1.99/0.67    spl4_21 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.99/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.99/0.67  fof(f289,plain,(
% 1.99/0.67    v1_relat_1(k2_funct_1(sK2)) | ~spl4_21),
% 1.99/0.67    inference(resolution,[],[f284,f106])).
% 1.99/0.67  fof(f284,plain,(
% 1.99/0.67    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 1.99/0.67    inference(avatar_component_clause,[],[f282])).
% 1.99/0.67  fof(f295,plain,(
% 1.99/0.67    ~spl4_22 | spl4_1 | ~spl4_7 | ~spl4_21),
% 1.99/0.67    inference(avatar_split_clause,[],[f290,f282,f142,f112,f292])).
% 1.99/0.67  fof(f292,plain,(
% 1.99/0.67    spl4_22 <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)),
% 1.99/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.99/0.67  fof(f112,plain,(
% 1.99/0.67    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.99/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.99/0.67  fof(f290,plain,(
% 1.99/0.67    ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | (spl4_1 | ~spl4_7 | ~spl4_21)),
% 1.99/0.67    inference(subsumption_resolution,[],[f286,f114])).
% 1.99/0.67  fof(f114,plain,(
% 1.99/0.67    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.99/0.67    inference(avatar_component_clause,[],[f112])).
% 1.99/0.67  fof(f286,plain,(
% 1.99/0.67    k2_funct_1(sK2) = sK3 | ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | (~spl4_7 | ~spl4_21)),
% 1.99/0.67    inference(resolution,[],[f284,f243])).
% 1.99/0.67  fof(f243,plain,(
% 1.99/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK3 = X0 | ~r2_relset_1(sK1,sK0,X0,sK3)) ) | ~spl4_7),
% 1.99/0.67    inference(resolution,[],[f97,f144])).
% 1.99/0.67  fof(f285,plain,(
% 1.99/0.67    spl4_21 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.99/0.67    inference(avatar_split_clause,[],[f280,f167,f162,f157,f137,f127,f282])).
% 1.99/0.67  fof(f280,plain,(
% 1.99/0.67    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.99/0.67    inference(subsumption_resolution,[],[f279,f169])).
% 1.99/0.67  fof(f279,plain,(
% 1.99/0.67    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.99/0.67    inference(subsumption_resolution,[],[f278,f164])).
% 1.99/0.67  fof(f278,plain,(
% 1.99/0.67    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.99/0.67    inference(subsumption_resolution,[],[f277,f159])).
% 1.99/0.67  fof(f277,plain,(
% 1.99/0.67    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 1.99/0.67    inference(subsumption_resolution,[],[f276,f129])).
% 1.99/0.67  fof(f276,plain,(
% 1.99/0.67    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.67    inference(trivial_inequality_removal,[],[f273])).
% 1.99/0.67  fof(f273,plain,(
% 1.99/0.67    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.67    inference(superposition,[],[f77,f139])).
% 1.99/0.67  fof(f259,plain,(
% 1.99/0.67    spl4_19 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.99/0.67    inference(avatar_split_clause,[],[f254,f167,f162,f157,f137,f127,f256])).
% 1.99/0.67  fof(f254,plain,(
% 1.99/0.67    v1_funct_1(k2_funct_1(sK2)) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.99/0.67    inference(subsumption_resolution,[],[f253,f169])).
% 1.99/0.67  fof(f253,plain,(
% 1.99/0.67    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.99/0.67    inference(subsumption_resolution,[],[f252,f164])).
% 1.99/0.67  fof(f252,plain,(
% 1.99/0.67    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.99/0.67    inference(subsumption_resolution,[],[f251,f159])).
% 1.99/0.67  fof(f251,plain,(
% 1.99/0.67    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 1.99/0.67    inference(subsumption_resolution,[],[f250,f129])).
% 1.99/0.67  fof(f250,plain,(
% 1.99/0.67    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.67    inference(trivial_inequality_removal,[],[f247])).
% 1.99/0.67  fof(f247,plain,(
% 1.99/0.67    sK1 != sK1 | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.99/0.67    inference(superposition,[],[f75,f139])).
% 1.99/0.67  fof(f221,plain,(
% 1.99/0.67    spl4_18 | ~spl4_6 | ~spl4_10),
% 1.99/0.67    inference(avatar_split_clause,[],[f220,f157,f137,f216])).
% 1.99/0.67  fof(f220,plain,(
% 1.99/0.67    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 1.99/0.67    inference(subsumption_resolution,[],[f213,f159])).
% 1.99/0.67  fof(f213,plain,(
% 1.99/0.67    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.99/0.67    inference(superposition,[],[f139,f105])).
% 1.99/0.67  fof(f201,plain,(
% 1.99/0.67    spl4_16 | ~spl4_7),
% 1.99/0.67    inference(avatar_split_clause,[],[f194,f142,f198])).
% 1.99/0.67  fof(f198,plain,(
% 1.99/0.67    spl4_16 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 1.99/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.99/0.67  fof(f194,plain,(
% 1.99/0.67    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_7),
% 1.99/0.67    inference(resolution,[],[f110,f144])).
% 1.99/0.67  fof(f110,plain,(
% 1.99/0.67    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.99/0.67    inference(duplicate_literal_removal,[],[f109])).
% 1.99/0.67  fof(f109,plain,(
% 1.99/0.67    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.67    inference(equality_resolution,[],[f98])).
% 1.99/0.67  fof(f98,plain,(
% 1.99/0.67    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.67    inference(cnf_transformation,[],[f60])).
% 1.99/0.67  fof(f190,plain,(
% 1.99/0.67    spl4_15 | ~spl4_10),
% 1.99/0.67    inference(avatar_split_clause,[],[f179,f157,f187])).
% 1.99/0.67  fof(f179,plain,(
% 1.99/0.67    v1_relat_1(sK2) | ~spl4_10),
% 1.99/0.67    inference(resolution,[],[f106,f159])).
% 1.99/0.67  fof(f185,plain,(
% 1.99/0.67    spl4_14 | ~spl4_7),
% 1.99/0.67    inference(avatar_split_clause,[],[f178,f142,f182])).
% 1.99/0.67  fof(f178,plain,(
% 1.99/0.67    v1_relat_1(sK3) | ~spl4_7),
% 1.99/0.67    inference(resolution,[],[f106,f144])).
% 1.99/0.67  fof(f176,plain,(
% 1.99/0.67    spl4_13 | ~spl4_5),
% 1.99/0.67    inference(avatar_split_clause,[],[f171,f132,f173])).
% 1.99/0.67  fof(f132,plain,(
% 1.99/0.67    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.99/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.99/0.67  fof(f171,plain,(
% 1.99/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.99/0.67    inference(backward_demodulation,[],[f134,f101])).
% 1.99/0.67  fof(f134,plain,(
% 1.99/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.99/0.67    inference(avatar_component_clause,[],[f132])).
% 1.99/0.67  fof(f170,plain,(
% 1.99/0.67    spl4_12),
% 1.99/0.67    inference(avatar_split_clause,[],[f61,f167])).
% 1.99/0.67  fof(f61,plain,(
% 1.99/0.67    v1_funct_1(sK2)),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f59,plain,(
% 1.99/0.67    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.99/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f58,f57])).
% 1.99/0.67  fof(f57,plain,(
% 1.99/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.99/0.67    introduced(choice_axiom,[])).
% 1.99/0.67  fof(f58,plain,(
% 1.99/0.67    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.99/0.67    introduced(choice_axiom,[])).
% 1.99/0.67  fof(f24,plain,(
% 1.99/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.99/0.67    inference(flattening,[],[f23])).
% 1.99/0.67  fof(f23,plain,(
% 1.99/0.67    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.99/0.67    inference(ennf_transformation,[],[f21])).
% 1.99/0.67  fof(f21,negated_conjecture,(
% 1.99/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.99/0.67    inference(negated_conjecture,[],[f20])).
% 1.99/0.67  fof(f20,conjecture,(
% 1.99/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.99/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.99/0.67  fof(f165,plain,(
% 1.99/0.67    spl4_11),
% 1.99/0.67    inference(avatar_split_clause,[],[f62,f162])).
% 1.99/0.67  fof(f62,plain,(
% 1.99/0.67    v1_funct_2(sK2,sK0,sK1)),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f160,plain,(
% 1.99/0.67    spl4_10),
% 1.99/0.67    inference(avatar_split_clause,[],[f63,f157])).
% 1.99/0.67  fof(f63,plain,(
% 1.99/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f155,plain,(
% 1.99/0.67    spl4_9),
% 1.99/0.67    inference(avatar_split_clause,[],[f64,f152])).
% 1.99/0.67  fof(f64,plain,(
% 1.99/0.67    v1_funct_1(sK3)),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f150,plain,(
% 1.99/0.67    spl4_8),
% 1.99/0.67    inference(avatar_split_clause,[],[f65,f147])).
% 1.99/0.67  fof(f65,plain,(
% 1.99/0.67    v1_funct_2(sK3,sK1,sK0)),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f145,plain,(
% 1.99/0.67    spl4_7),
% 1.99/0.67    inference(avatar_split_clause,[],[f66,f142])).
% 1.99/0.67  fof(f66,plain,(
% 1.99/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f140,plain,(
% 1.99/0.67    spl4_6),
% 1.99/0.67    inference(avatar_split_clause,[],[f67,f137])).
% 1.99/0.67  fof(f67,plain,(
% 1.99/0.67    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f135,plain,(
% 1.99/0.67    spl4_5),
% 1.99/0.67    inference(avatar_split_clause,[],[f68,f132])).
% 1.99/0.67  fof(f68,plain,(
% 1.99/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f130,plain,(
% 1.99/0.67    spl4_4),
% 1.99/0.67    inference(avatar_split_clause,[],[f69,f127])).
% 1.99/0.67  fof(f69,plain,(
% 1.99/0.67    v2_funct_1(sK2)),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f125,plain,(
% 1.99/0.67    ~spl4_3),
% 1.99/0.67    inference(avatar_split_clause,[],[f70,f122])).
% 1.99/0.67  fof(f70,plain,(
% 1.99/0.67    k1_xboole_0 != sK0),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f120,plain,(
% 1.99/0.67    ~spl4_2),
% 1.99/0.67    inference(avatar_split_clause,[],[f71,f117])).
% 1.99/0.67  fof(f71,plain,(
% 1.99/0.67    k1_xboole_0 != sK1),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  fof(f115,plain,(
% 1.99/0.67    ~spl4_1),
% 1.99/0.67    inference(avatar_split_clause,[],[f72,f112])).
% 1.99/0.67  fof(f72,plain,(
% 1.99/0.67    k2_funct_1(sK2) != sK3),
% 1.99/0.67    inference(cnf_transformation,[],[f59])).
% 1.99/0.67  % SZS output end Proof for theBenchmark
% 1.99/0.67  % (14823)------------------------------
% 1.99/0.67  % (14823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.67  % (14823)Termination reason: Refutation
% 1.99/0.67  
% 1.99/0.67  % (14823)Memory used [KB]: 7291
% 1.99/0.67  % (14823)Time elapsed: 0.221 s
% 1.99/0.67  % (14823)------------------------------
% 1.99/0.67  % (14823)------------------------------
% 1.99/0.67  % (14801)Success in time 0.294 s
%------------------------------------------------------------------------------
