%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:41 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  359 ( 864 expanded)
%              Number of leaves         :   70 ( 378 expanded)
%              Depth                    :   16
%              Number of atoms          : 1771 (3972 expanded)
%              Number of equality atoms :  296 ( 894 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f170,f179,f184,f195,f210,f243,f269,f279,f289,f301,f323,f337,f349,f389,f398,f415,f460,f476,f488,f497,f506,f528,f610,f619,f842,f863,f898,f914,f989,f1021,f1046,f1048,f1049,f1080,f1094,f1095])).

fof(f1095,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1094,plain,
    ( sK2 != k2_funct_1(sK3)
    | k1_relat_1(sK2) != k2_relat_1(k6_relat_1(sK0))
    | sK0 != k2_relat_1(k6_relat_1(sK0))
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1080,plain,
    ( spl4_89
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_36
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f1075,f503,f453,f445,f176,f146,f1077])).

fof(f1077,plain,
    ( spl4_89
  <=> sK0 = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f146,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f176,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f445,plain,
    ( spl4_36
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f453,plain,
    ( spl4_37
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f503,plain,
    ( spl4_43
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1075,plain,
    ( sK0 = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_36
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f1074,f447])).

fof(f447,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f445])).

fof(f1074,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1073,f178])).

fof(f178,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f176])).

fof(f1073,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1072,f148])).

fof(f148,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1072,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f1052,f454])).

fof(f454,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f453])).

fof(f1052,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43 ),
    inference(superposition,[],[f77,f505])).

fof(f505,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f503])).

fof(f77,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f1049,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1048,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1046,plain,
    ( ~ spl4_82
    | ~ spl4_84
    | spl4_85
    | ~ spl4_86
    | ~ spl4_87
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_36
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f1029,f494,f457,f445,f176,f146,f1043,f1039,f1035,f1031,f986])).

fof(f986,plain,
    ( spl4_82
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1031,plain,
    ( spl4_84
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1035,plain,
    ( spl4_85
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f1039,plain,
    ( spl4_86
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1043,plain,
    ( spl4_87
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f457,plain,
    ( spl4_38
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f494,plain,
    ( spl4_42
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1029,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_36
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1028,f447])).

fof(f1028,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_38
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1027,f459])).

fof(f459,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f457])).

fof(f1027,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1026,f178])).

fof(f1026,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f996,f148])).

fof(f996,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_42 ),
    inference(superposition,[],[f75,f496])).

fof(f496,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f494])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1021,plain,
    ( spl4_69
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_42
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f1020,f525,f494,f453,f176,f146,f911])).

fof(f911,plain,
    ( spl4_69
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f525,plain,
    ( spl4_45
  <=> sK1 = k1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1020,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_42
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f1019,f527])).

fof(f527,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f525])).

fof(f1019,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1018,f178])).

fof(f1018,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1017,f148])).

fof(f1017,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f993,f454])).

fof(f993,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_42 ),
    inference(superposition,[],[f78,f496])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f989,plain,
    ( spl4_82
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f973,f473,f986])).

fof(f473,plain,
    ( spl4_40
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f973,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_40 ),
    inference(resolution,[],[f475,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f475,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f473])).

fof(f914,plain,
    ( ~ spl4_37
    | spl4_68
    | ~ spl4_69
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_36
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f905,f616,f445,f205,f181,f176,f161,f146,f911,f907,f453])).

fof(f907,plain,
    ( spl4_68
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f161,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f181,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f205,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f616,plain,
    ( spl4_53
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f905,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_36
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f904,f207])).

fof(f207,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f205])).

fof(f904,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_53 ),
    inference(trivial_inequality_removal,[],[f903])).

fof(f903,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_36
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f902,f447])).

fof(f902,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f901,f178])).

fof(f901,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f900,f148])).

fof(f900,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f899,f183])).

fof(f183,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f899,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f848,f163])).

fof(f163,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f848,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_53 ),
    inference(superposition,[],[f75,f618])).

fof(f618,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f616])).

fof(f898,plain,
    ( spl4_37
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f897,f607,f386,f161,f156,f151,f146,f141,f136,f131,f116,f453])).

fof(f116,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f131,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f136,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f141,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f151,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f156,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f386,plain,
    ( spl4_34
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f607,plain,
    ( spl4_51
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f897,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f896,f148])).

fof(f896,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f895,f143])).

fof(f143,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f895,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f894,f138])).

fof(f138,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f894,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f881,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f881,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f873,f388])).

fof(f388,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f386])).

fof(f873,plain,
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
    inference(superposition,[],[f426,f609])).

fof(f609,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f607])).

fof(f426,plain,
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
    inference(subsumption_resolution,[],[f425,f163])).

fof(f425,plain,
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
    inference(subsumption_resolution,[],[f424,f158])).

fof(f158,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f424,plain,
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
    inference(subsumption_resolution,[],[f423,f153])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f423,plain,
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
    inference(trivial_inequality_removal,[],[f420])).

fof(f420,plain,
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
    inference(superposition,[],[f88,f133])).

fof(f133,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f41])).

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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f863,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_50 ),
    inference(avatar_contradiction_clause,[],[f862])).

% (13544)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f862,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_50 ),
    inference(subsumption_resolution,[],[f861,f163])).

fof(f861,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_50 ),
    inference(subsumption_resolution,[],[f860,f153])).

fof(f860,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_50 ),
    inference(subsumption_resolution,[],[f859,f148])).

fof(f859,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_50 ),
    inference(subsumption_resolution,[],[f856,f138])).

fof(f856,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_50 ),
    inference(resolution,[],[f605,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f605,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl4_50
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f842,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_52 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_52 ),
    inference(unit_resulting_resolution,[],[f163,f148,f153,f138,f614,f307])).

fof(f307,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
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
    inference(superposition,[],[f97,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f614,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f612])).

fof(f612,plain,
    ( spl4_52
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f619,plain,
    ( ~ spl4_52
    | spl4_53
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f600,f298,f616,f612])).

fof(f298,plain,
    ( spl4_25
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f600,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_25 ),
    inference(resolution,[],[f229,f300])).

fof(f300,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f298])).

fof(f229,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f91,f171])).

fof(f171,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f94,f95])).

fof(f95,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f610,plain,
    ( ~ spl4_50
    | spl4_51
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f599,f167,f607,f603])).

fof(f167,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f599,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f229,f169])).

fof(f169,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f528,plain,
    ( spl4_45
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f523,f334,f205,f181,f161,f121,f525])).

fof(f121,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f334,plain,
    ( spl4_27
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f523,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f522,f207])).

fof(f522,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f521,f183])).

fof(f521,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f520,f163])).

fof(f520,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f508,f123])).

fof(f123,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f508,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_27 ),
    inference(superposition,[],[f76,f336])).

fof(f336,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f334])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f506,plain,
    ( spl4_43
    | ~ spl4_37
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f501,f412,f146,f141,f136,f116,f453,f503])).

fof(f412,plain,
    ( spl4_35
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f501,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f500,f148])).

fof(f500,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f499,f143])).

fof(f499,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f498,f138])).

fof(f498,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f436,f118])).

fof(f436,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f435])).

fof(f435,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f309,f414])).

fof(f414,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f412])).

fof(f309,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f71,f95])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f497,plain,
    ( spl4_42
    | ~ spl4_37
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f492,f412,f146,f141,f136,f116,f453,f494])).

fof(f492,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f491,f148])).

fof(f491,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f490,f143])).

fof(f490,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f489,f138])).

fof(f489,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f437,f118])).

fof(f437,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f434])).

fof(f434,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f308,f414])).

fof(f308,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f70,f95])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f488,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f487,f412,f136,f445])).

fof(f487,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f433,f138])).

fof(f433,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_35 ),
    inference(superposition,[],[f99,f414])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f476,plain,
    ( ~ spl4_37
    | spl4_40
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f471,f412,f146,f141,f136,f473,f453])).

fof(f471,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f470,f148])).

fof(f470,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f469,f143])).

fof(f469,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f440,f138])).

fof(f440,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f430])).

fof(f430,plain,
    ( sK0 != sK0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f74,f414])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f460,plain,
    ( ~ spl4_37
    | spl4_38
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f451,f412,f146,f141,f136,f457,f453])).

fof(f451,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f450,f148])).

fof(f450,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f449,f143])).

fof(f449,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f442,f138])).

fof(f442,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f428])).

fof(f428,plain,
    ( sK0 != sK0
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f72,f414])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f415,plain,
    ( spl4_35
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f410,f167,f161,f156,f151,f146,f141,f136,f412])).

fof(f410,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f409,f148])).

fof(f409,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f408,f143])).

fof(f408,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f407,f138])).

fof(f407,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f406,f163])).

fof(f406,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f405,f158])).

fof(f405,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f402,f153])).

fof(f402,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f401,f169])).

fof(f401,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f93,f95])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f398,plain,
    ( ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | spl4_30 ),
    inference(subsumption_resolution,[],[f396,f183])).

fof(f396,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | spl4_30 ),
    inference(subsumption_resolution,[],[f395,f163])).

fof(f395,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | spl4_30 ),
    inference(subsumption_resolution,[],[f393,f123])).

fof(f393,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_30 ),
    inference(resolution,[],[f366,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f366,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl4_30
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f389,plain,
    ( ~ spl4_30
    | spl4_34
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f384,f320,f286,f240,f181,f161,f121,f386,f364])).

fof(f240,plain,
    ( spl4_19
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f286,plain,
    ( spl4_24
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f320,plain,
    ( spl4_26
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f384,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f383,f183])).

fof(f383,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f382,f163])).

fof(f382,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f381,f288])).

fof(f288,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f286])).

fof(f381,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f380,f242])).

fof(f242,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f380,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f341,f123])).

fof(f341,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f90,f322])).

fof(f322,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f320])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

fof(f349,plain,
    ( spl4_28
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f344,f320,f181,f161,f121,f346])).

fof(f346,plain,
    ( spl4_28
  <=> k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f344,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f343,f183])).

fof(f343,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f342,f163])).

fof(f342,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f338,f123])).

fof(f338,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f79,f322])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f337,plain,
    ( spl4_27
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f332,f161,f156,f151,f131,f121,f111,f334])).

fof(f111,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f332,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f331,f163])).

fof(f331,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f330,f158])).

fof(f330,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f329,f153])).

fof(f329,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f328,f123])).

fof(f328,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f327,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f327,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f309,f133])).

fof(f323,plain,
    ( spl4_26
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f318,f161,f156,f151,f131,f121,f111,f320])).

fof(f318,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f317,f163])).

fof(f317,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f316,f158])).

fof(f316,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f315,f153])).

fof(f315,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f314,f123])).

fof(f314,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f313,f113])).

fof(f313,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f310])).

fof(f310,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f308,f133])).

fof(f301,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f296,f167,f161,f151,f146,f136,f298])).

fof(f296,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f295,f163])).

fof(f295,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f294,f153])).

fof(f294,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f293,f148])).

fof(f293,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f290,f138])).

fof(f290,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f169,f98])).

fof(f289,plain,
    ( spl4_24
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f273,f266,f286])).

fof(f266,plain,
    ( spl4_21
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f273,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(resolution,[],[f268,f100])).

fof(f268,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f266])).

fof(f279,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f274,f266,f136,f106,f276])).

fof(f276,plain,
    ( spl4_22
  <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f106,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f274,plain,
    ( ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | spl4_1
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f270,f108])).

fof(f108,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f270,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(resolution,[],[f268,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | sK3 = X0
        | ~ r2_relset_1(sK1,sK0,X0,sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f91,f138])).

fof(f269,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f264,f161,f156,f151,f131,f121,f266])).

fof(f264,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f263,f163])).

fof(f263,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f262,f158])).

fof(f262,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f261,f153])).

fof(f261,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f260,f123])).

fof(f260,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f257])).

fof(f257,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f74,f133])).

fof(f243,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f238,f161,f156,f151,f131,f121,f240])).

fof(f238,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f237,f163])).

fof(f237,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f236,f158])).

fof(f236,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f235,f153])).

fof(f235,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f234,f123])).

fof(f234,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,
    ( sK1 != sK1
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f72,f133])).

fof(f210,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f209,f151,f131,f205])).

fof(f209,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f202,f153])).

fof(f202,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f133,f99])).

fof(f195,plain,
    ( spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f188,f136,f192])).

fof(f192,plain,
    ( spl4_16
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f188,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f104,f138])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f184,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f173,f151,f181])).

fof(f173,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f100,f153])).

fof(f179,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f172,f136,f176])).

fof(f172,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f100,f138])).

fof(f170,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f165,f126,f167])).

fof(f126,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f165,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f128,f95])).

fof(f128,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f164,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f58,f161])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f55,f54])).

fof(f54,plain,
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

fof(f55,plain,
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
    inference(flattening,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f159,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f59,f156])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f154,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f60,f151])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f149,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f61,f146])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f144,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f139,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f63,f136])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f134,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f64,f131])).

fof(f64,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f129,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f65,f126])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f124,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f66,f121])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f119,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f67,f116])).

fof(f67,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f68,f111])).

fof(f68,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f69,f106])).

fof(f69,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:45:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (13523)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (13524)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (13539)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (13541)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (13531)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (13540)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (13533)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (13532)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (13525)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.40/0.57  % (13521)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.57  % (13522)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.58  % (13519)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.69/0.60  % (13545)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.69/0.60  % (13535)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.69/0.60  % (13518)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.69/0.61  % (13537)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.69/0.61  % (13527)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.69/0.61  % (13538)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.61  % (13520)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.69/0.61  % (13529)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.69/0.62  % (13530)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.69/0.62  % (13547)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.69/0.62  % (13526)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.69/0.63  % (13543)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.69/0.64  % (13534)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.69/0.64  % (13534)Refutation not found, incomplete strategy% (13534)------------------------------
% 1.69/0.64  % (13534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.64  % (13534)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.64  
% 1.69/0.64  % (13534)Memory used [KB]: 10746
% 1.69/0.64  % (13534)Time elapsed: 0.212 s
% 1.69/0.64  % (13534)------------------------------
% 1.69/0.64  % (13534)------------------------------
% 1.69/0.64  % (13539)Refutation found. Thanks to Tanya!
% 1.69/0.64  % SZS status Theorem for theBenchmark
% 1.69/0.64  % SZS output start Proof for theBenchmark
% 1.69/0.65  fof(f1096,plain,(
% 1.69/0.65    $false),
% 1.69/0.65    inference(avatar_sat_refutation,[],[f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f170,f179,f184,f195,f210,f243,f269,f279,f289,f301,f323,f337,f349,f389,f398,f415,f460,f476,f488,f497,f506,f528,f610,f619,f842,f863,f898,f914,f989,f1021,f1046,f1048,f1049,f1080,f1094,f1095])).
% 1.69/0.65  fof(f1095,plain,(
% 1.69/0.65    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | ~r2_relset_1(sK1,sK0,sK3,sK3)),
% 1.69/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.69/0.65  fof(f1094,plain,(
% 1.69/0.65    sK2 != k2_funct_1(sK3) | k1_relat_1(sK2) != k2_relat_1(k6_relat_1(sK0)) | sK0 != k2_relat_1(k6_relat_1(sK0)) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.69/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.69/0.65  fof(f1080,plain,(
% 1.69/0.65    spl4_89 | ~spl4_9 | ~spl4_14 | ~spl4_36 | ~spl4_37 | ~spl4_43),
% 1.69/0.65    inference(avatar_split_clause,[],[f1075,f503,f453,f445,f176,f146,f1077])).
% 1.69/0.65  fof(f1077,plain,(
% 1.69/0.65    spl4_89 <=> sK0 = k2_relat_1(k6_relat_1(sK0))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 1.69/0.65  fof(f146,plain,(
% 1.69/0.65    spl4_9 <=> v1_funct_1(sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.69/0.65  fof(f176,plain,(
% 1.69/0.65    spl4_14 <=> v1_relat_1(sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.69/0.65  fof(f445,plain,(
% 1.69/0.65    spl4_36 <=> sK0 = k2_relat_1(sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.69/0.65  fof(f453,plain,(
% 1.69/0.65    spl4_37 <=> v2_funct_1(sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.69/0.65  fof(f503,plain,(
% 1.69/0.65    spl4_43 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.69/0.65  fof(f1075,plain,(
% 1.69/0.65    sK0 = k2_relat_1(k6_relat_1(sK0)) | (~spl4_9 | ~spl4_14 | ~spl4_36 | ~spl4_37 | ~spl4_43)),
% 1.69/0.65    inference(forward_demodulation,[],[f1074,f447])).
% 1.69/0.65  fof(f447,plain,(
% 1.69/0.65    sK0 = k2_relat_1(sK3) | ~spl4_36),
% 1.69/0.65    inference(avatar_component_clause,[],[f445])).
% 1.69/0.65  fof(f1074,plain,(
% 1.69/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_43)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1073,f178])).
% 1.69/0.65  fof(f178,plain,(
% 1.69/0.65    v1_relat_1(sK3) | ~spl4_14),
% 1.69/0.65    inference(avatar_component_clause,[],[f176])).
% 1.69/0.65  fof(f1073,plain,(
% 1.69/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_37 | ~spl4_43)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1072,f148])).
% 1.69/0.65  fof(f148,plain,(
% 1.69/0.65    v1_funct_1(sK3) | ~spl4_9),
% 1.69/0.65    inference(avatar_component_clause,[],[f146])).
% 1.69/0.65  fof(f1072,plain,(
% 1.69/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_37 | ~spl4_43)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1052,f454])).
% 1.69/0.65  fof(f454,plain,(
% 1.69/0.65    v2_funct_1(sK3) | ~spl4_37),
% 1.69/0.65    inference(avatar_component_clause,[],[f453])).
% 1.69/0.65  fof(f1052,plain,(
% 1.69/0.65    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_43),
% 1.69/0.65    inference(superposition,[],[f77,f505])).
% 1.69/0.65  fof(f505,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_43),
% 1.69/0.65    inference(avatar_component_clause,[],[f503])).
% 1.69/0.65  fof(f77,plain,(
% 1.69/0.65    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f31])).
% 1.69/0.65  fof(f31,plain,(
% 1.69/0.65    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.65    inference(flattening,[],[f30])).
% 1.69/0.65  fof(f30,plain,(
% 1.69/0.65    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f5])).
% 1.69/0.65  fof(f5,axiom,(
% 1.69/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.69/0.65  fof(f1049,plain,(
% 1.69/0.65    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.69/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.69/0.65  fof(f1048,plain,(
% 1.69/0.65    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.69/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.69/0.65  fof(f1046,plain,(
% 1.69/0.65    ~spl4_82 | ~spl4_84 | spl4_85 | ~spl4_86 | ~spl4_87 | ~spl4_9 | ~spl4_14 | ~spl4_36 | ~spl4_38 | ~spl4_42),
% 1.69/0.65    inference(avatar_split_clause,[],[f1029,f494,f457,f445,f176,f146,f1043,f1039,f1035,f1031,f986])).
% 1.69/0.65  fof(f986,plain,(
% 1.69/0.65    spl4_82 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 1.69/0.65  fof(f1031,plain,(
% 1.69/0.65    spl4_84 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 1.69/0.65  fof(f1035,plain,(
% 1.69/0.65    spl4_85 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 1.69/0.65  fof(f1039,plain,(
% 1.69/0.65    spl4_86 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 1.69/0.65  fof(f1043,plain,(
% 1.69/0.65    spl4_87 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 1.69/0.65  fof(f457,plain,(
% 1.69/0.65    spl4_38 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.69/0.65  fof(f494,plain,(
% 1.69/0.65    spl4_42 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.69/0.65  fof(f1029,plain,(
% 1.69/0.65    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_36 | ~spl4_38 | ~spl4_42)),
% 1.69/0.65    inference(forward_demodulation,[],[f1028,f447])).
% 1.69/0.65  fof(f1028,plain,(
% 1.69/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_38 | ~spl4_42)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1027,f459])).
% 1.69/0.65  fof(f459,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK3)) | ~spl4_38),
% 1.69/0.65    inference(avatar_component_clause,[],[f457])).
% 1.69/0.65  fof(f1027,plain,(
% 1.69/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_42)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1026,f178])).
% 1.69/0.65  fof(f1026,plain,(
% 1.69/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_42)),
% 1.69/0.65    inference(subsumption_resolution,[],[f996,f148])).
% 1.69/0.65  fof(f996,plain,(
% 1.69/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_42),
% 1.69/0.65    inference(superposition,[],[f75,f496])).
% 1.69/0.65  fof(f496,plain,(
% 1.69/0.65    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_42),
% 1.69/0.65    inference(avatar_component_clause,[],[f494])).
% 1.69/0.65  fof(f75,plain,(
% 1.69/0.65    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f29])).
% 1.69/0.65  fof(f29,plain,(
% 1.69/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.65    inference(flattening,[],[f28])).
% 1.69/0.65  fof(f28,plain,(
% 1.69/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f6])).
% 1.69/0.65  fof(f6,axiom,(
% 1.69/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.69/0.65  fof(f1021,plain,(
% 1.69/0.65    spl4_69 | ~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_42 | ~spl4_45),
% 1.69/0.65    inference(avatar_split_clause,[],[f1020,f525,f494,f453,f176,f146,f911])).
% 1.69/0.65  fof(f911,plain,(
% 1.69/0.65    spl4_69 <=> sK1 = k1_relat_1(sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.69/0.65  fof(f525,plain,(
% 1.69/0.65    spl4_45 <=> sK1 = k1_relat_1(k6_relat_1(sK1))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.69/0.65  fof(f1020,plain,(
% 1.69/0.65    sK1 = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_42 | ~spl4_45)),
% 1.69/0.65    inference(forward_demodulation,[],[f1019,f527])).
% 1.69/0.65  fof(f527,plain,(
% 1.69/0.65    sK1 = k1_relat_1(k6_relat_1(sK1)) | ~spl4_45),
% 1.69/0.65    inference(avatar_component_clause,[],[f525])).
% 1.69/0.65  fof(f1019,plain,(
% 1.69/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_37 | ~spl4_42)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1018,f178])).
% 1.69/0.65  fof(f1018,plain,(
% 1.69/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_37 | ~spl4_42)),
% 1.69/0.65    inference(subsumption_resolution,[],[f1017,f148])).
% 1.69/0.65  fof(f1017,plain,(
% 1.69/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_37 | ~spl4_42)),
% 1.69/0.65    inference(subsumption_resolution,[],[f993,f454])).
% 1.69/0.65  fof(f993,plain,(
% 1.69/0.65    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_42),
% 1.69/0.65    inference(superposition,[],[f78,f496])).
% 1.69/0.65  fof(f78,plain,(
% 1.69/0.65    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f33,plain,(
% 1.69/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.65    inference(flattening,[],[f32])).
% 1.69/0.65  fof(f32,plain,(
% 1.69/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f4])).
% 1.69/0.65  fof(f4,axiom,(
% 1.69/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 1.69/0.65  fof(f989,plain,(
% 1.69/0.65    spl4_82 | ~spl4_40),
% 1.69/0.65    inference(avatar_split_clause,[],[f973,f473,f986])).
% 1.69/0.65  fof(f473,plain,(
% 1.69/0.65    spl4_40 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.69/0.65  fof(f973,plain,(
% 1.69/0.65    v1_relat_1(k2_funct_1(sK3)) | ~spl4_40),
% 1.69/0.65    inference(resolution,[],[f475,f100])).
% 1.69/0.65  fof(f100,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f53])).
% 1.69/0.65  fof(f53,plain,(
% 1.69/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.65    inference(ennf_transformation,[],[f8])).
% 1.69/0.65  fof(f8,axiom,(
% 1.69/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.69/0.65  fof(f475,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_40),
% 1.69/0.65    inference(avatar_component_clause,[],[f473])).
% 1.69/0.65  fof(f914,plain,(
% 1.69/0.65    ~spl4_37 | spl4_68 | ~spl4_69 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_36 | ~spl4_53),
% 1.69/0.65    inference(avatar_split_clause,[],[f905,f616,f445,f205,f181,f176,f161,f146,f911,f907,f453])).
% 1.69/0.65  fof(f907,plain,(
% 1.69/0.65    spl4_68 <=> sK2 = k2_funct_1(sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.69/0.65  fof(f161,plain,(
% 1.69/0.65    spl4_12 <=> v1_funct_1(sK2)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.69/0.65  fof(f181,plain,(
% 1.69/0.65    spl4_15 <=> v1_relat_1(sK2)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.69/0.65  fof(f205,plain,(
% 1.69/0.65    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.69/0.65  fof(f616,plain,(
% 1.69/0.65    spl4_53 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.69/0.65  fof(f905,plain,(
% 1.69/0.65    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_36 | ~spl4_53)),
% 1.69/0.65    inference(forward_demodulation,[],[f904,f207])).
% 1.69/0.65  fof(f207,plain,(
% 1.69/0.65    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.69/0.65    inference(avatar_component_clause,[],[f205])).
% 1.69/0.65  fof(f904,plain,(
% 1.69/0.65    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_36 | ~spl4_53)),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f903])).
% 1.69/0.65  fof(f903,plain,(
% 1.69/0.65    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_36 | ~spl4_53)),
% 1.69/0.65    inference(forward_demodulation,[],[f902,f447])).
% 1.69/0.65  fof(f902,plain,(
% 1.69/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_53)),
% 1.69/0.65    inference(subsumption_resolution,[],[f901,f178])).
% 1.69/0.65  fof(f901,plain,(
% 1.69/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_53)),
% 1.69/0.65    inference(subsumption_resolution,[],[f900,f148])).
% 1.69/0.65  fof(f900,plain,(
% 1.69/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_53)),
% 1.69/0.65    inference(subsumption_resolution,[],[f899,f183])).
% 1.69/0.65  fof(f183,plain,(
% 1.69/0.65    v1_relat_1(sK2) | ~spl4_15),
% 1.69/0.65    inference(avatar_component_clause,[],[f181])).
% 1.69/0.65  fof(f899,plain,(
% 1.69/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_53)),
% 1.69/0.65    inference(subsumption_resolution,[],[f848,f163])).
% 1.69/0.65  fof(f163,plain,(
% 1.69/0.65    v1_funct_1(sK2) | ~spl4_12),
% 1.69/0.65    inference(avatar_component_clause,[],[f161])).
% 1.69/0.65  fof(f848,plain,(
% 1.69/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_53),
% 1.69/0.65    inference(superposition,[],[f75,f618])).
% 1.69/0.65  fof(f618,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_53),
% 1.69/0.65    inference(avatar_component_clause,[],[f616])).
% 1.69/0.65  fof(f898,plain,(
% 1.69/0.65    spl4_37 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_34 | ~spl4_51),
% 1.69/0.65    inference(avatar_split_clause,[],[f897,f607,f386,f161,f156,f151,f146,f141,f136,f131,f116,f453])).
% 1.69/0.65  fof(f116,plain,(
% 1.69/0.65    spl4_3 <=> k1_xboole_0 = sK0),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.69/0.65  fof(f131,plain,(
% 1.69/0.65    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.69/0.65  fof(f136,plain,(
% 1.69/0.65    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.69/0.65  fof(f141,plain,(
% 1.69/0.65    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.69/0.65  fof(f151,plain,(
% 1.69/0.65    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.69/0.65  fof(f156,plain,(
% 1.69/0.65    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.69/0.65  fof(f386,plain,(
% 1.69/0.65    spl4_34 <=> v2_funct_1(k6_relat_1(sK0))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.69/0.65  fof(f607,plain,(
% 1.69/0.65    spl4_51 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.69/0.65  fof(f897,plain,(
% 1.69/0.65    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_34 | ~spl4_51)),
% 1.69/0.65    inference(subsumption_resolution,[],[f896,f148])).
% 1.69/0.65  fof(f896,plain,(
% 1.69/0.65    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_34 | ~spl4_51)),
% 1.69/0.65    inference(subsumption_resolution,[],[f895,f143])).
% 1.69/0.65  fof(f143,plain,(
% 1.69/0.65    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.69/0.65    inference(avatar_component_clause,[],[f141])).
% 1.69/0.65  fof(f895,plain,(
% 1.69/0.65    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_34 | ~spl4_51)),
% 1.69/0.65    inference(subsumption_resolution,[],[f894,f138])).
% 1.69/0.65  fof(f138,plain,(
% 1.69/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.69/0.65    inference(avatar_component_clause,[],[f136])).
% 1.69/0.65  fof(f894,plain,(
% 1.69/0.65    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_34 | ~spl4_51)),
% 1.69/0.65    inference(subsumption_resolution,[],[f881,f118])).
% 1.69/0.65  fof(f118,plain,(
% 1.69/0.65    k1_xboole_0 != sK0 | spl4_3),
% 1.69/0.65    inference(avatar_component_clause,[],[f116])).
% 1.69/0.65  fof(f881,plain,(
% 1.69/0.65    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_34 | ~spl4_51)),
% 1.69/0.65    inference(subsumption_resolution,[],[f873,f388])).
% 1.69/0.65  fof(f388,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~spl4_34),
% 1.69/0.65    inference(avatar_component_clause,[],[f386])).
% 1.69/0.65  fof(f873,plain,(
% 1.69/0.65    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_51)),
% 1.69/0.65    inference(superposition,[],[f426,f609])).
% 1.69/0.65  fof(f609,plain,(
% 1.69/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_51),
% 1.69/0.65    inference(avatar_component_clause,[],[f607])).
% 1.69/0.65  fof(f426,plain,(
% 1.69/0.65    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.69/0.65    inference(subsumption_resolution,[],[f425,f163])).
% 1.69/0.65  fof(f425,plain,(
% 1.69/0.65    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.69/0.65    inference(subsumption_resolution,[],[f424,f158])).
% 1.69/0.65  fof(f158,plain,(
% 1.69/0.65    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.69/0.65    inference(avatar_component_clause,[],[f156])).
% 1.69/0.65  fof(f424,plain,(
% 1.69/0.65    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.69/0.65    inference(subsumption_resolution,[],[f423,f153])).
% 1.69/0.65  fof(f153,plain,(
% 1.69/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.69/0.65    inference(avatar_component_clause,[],[f151])).
% 1.69/0.65  fof(f423,plain,(
% 1.69/0.65    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f420])).
% 1.69/0.65  fof(f420,plain,(
% 1.69/0.65    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.69/0.65    inference(superposition,[],[f88,f133])).
% 1.69/0.65  fof(f133,plain,(
% 1.69/0.65    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.69/0.65    inference(avatar_component_clause,[],[f131])).
% 1.69/0.65  fof(f88,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f41])).
% 1.69/0.65  fof(f41,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.69/0.65    inference(flattening,[],[f40])).
% 1.69/0.65  fof(f40,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.69/0.65    inference(ennf_transformation,[],[f16])).
% 1.69/0.65  fof(f16,axiom,(
% 1.69/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.69/0.65  fof(f863,plain,(
% 1.69/0.65    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_50),
% 1.69/0.65    inference(avatar_contradiction_clause,[],[f862])).
% 1.69/0.65  % (13544)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.69/0.65  fof(f862,plain,(
% 1.69/0.65    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_50)),
% 1.69/0.65    inference(subsumption_resolution,[],[f861,f163])).
% 1.69/0.65  fof(f861,plain,(
% 1.69/0.65    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_50)),
% 1.69/0.65    inference(subsumption_resolution,[],[f860,f153])).
% 1.69/0.65  fof(f860,plain,(
% 1.69/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_50)),
% 1.69/0.65    inference(subsumption_resolution,[],[f859,f148])).
% 1.69/0.65  fof(f859,plain,(
% 1.69/0.65    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_50)),
% 1.69/0.65    inference(subsumption_resolution,[],[f856,f138])).
% 1.69/0.65  fof(f856,plain,(
% 1.69/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_50),
% 1.69/0.65    inference(resolution,[],[f605,f97])).
% 1.69/0.65  fof(f97,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f49])).
% 1.69/0.65  fof(f49,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.65    inference(flattening,[],[f48])).
% 1.69/0.65  fof(f48,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.65    inference(ennf_transformation,[],[f11])).
% 1.69/0.65  fof(f11,axiom,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.69/0.65  fof(f605,plain,(
% 1.69/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_50),
% 1.69/0.65    inference(avatar_component_clause,[],[f603])).
% 1.69/0.65  fof(f603,plain,(
% 1.69/0.65    spl4_50 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.69/0.65  fof(f842,plain,(
% 1.69/0.65    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_52),
% 1.69/0.65    inference(avatar_contradiction_clause,[],[f840])).
% 1.69/0.65  fof(f840,plain,(
% 1.69/0.65    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_52)),
% 1.69/0.65    inference(unit_resulting_resolution,[],[f163,f148,f153,f138,f614,f307])).
% 1.69/0.65  fof(f307,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.69/0.65    inference(duplicate_literal_removal,[],[f306])).
% 1.69/0.65  fof(f306,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.69/0.65    inference(superposition,[],[f97,f98])).
% 1.69/0.65  fof(f98,plain,(
% 1.69/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f51])).
% 1.69/0.65  fof(f51,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.65    inference(flattening,[],[f50])).
% 1.69/0.65  fof(f50,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.65    inference(ennf_transformation,[],[f13])).
% 1.69/0.65  fof(f13,axiom,(
% 1.69/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.69/0.65  fof(f614,plain,(
% 1.69/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_52),
% 1.69/0.65    inference(avatar_component_clause,[],[f612])).
% 1.69/0.65  fof(f612,plain,(
% 1.69/0.65    spl4_52 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.69/0.65  fof(f619,plain,(
% 1.69/0.65    ~spl4_52 | spl4_53 | ~spl4_25),
% 1.69/0.65    inference(avatar_split_clause,[],[f600,f298,f616,f612])).
% 1.69/0.65  fof(f298,plain,(
% 1.69/0.65    spl4_25 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.69/0.65  fof(f600,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_25),
% 1.69/0.65    inference(resolution,[],[f229,f300])).
% 1.69/0.65  fof(f300,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_25),
% 1.69/0.65    inference(avatar_component_clause,[],[f298])).
% 1.69/0.65  fof(f229,plain,(
% 1.69/0.65    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.69/0.65    inference(resolution,[],[f91,f171])).
% 1.69/0.65  fof(f171,plain,(
% 1.69/0.65    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.69/0.65    inference(forward_demodulation,[],[f94,f95])).
% 1.69/0.65  fof(f95,plain,(
% 1.69/0.65    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f14])).
% 1.69/0.65  fof(f14,axiom,(
% 1.69/0.65    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.69/0.65  fof(f94,plain,(
% 1.69/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.69/0.65    inference(cnf_transformation,[],[f21])).
% 1.69/0.65  fof(f21,plain,(
% 1.69/0.65    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.69/0.65    inference(pure_predicate_removal,[],[f12])).
% 1.69/0.65  fof(f12,axiom,(
% 1.69/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.69/0.65  fof(f91,plain,(
% 1.69/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.65    inference(cnf_transformation,[],[f57])).
% 1.69/0.65  fof(f57,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.65    inference(nnf_transformation,[],[f45])).
% 1.69/0.65  fof(f45,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.65    inference(flattening,[],[f44])).
% 1.69/0.65  fof(f44,plain,(
% 1.69/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.69/0.65    inference(ennf_transformation,[],[f10])).
% 1.69/0.65  fof(f10,axiom,(
% 1.69/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.69/0.65  fof(f610,plain,(
% 1.69/0.65    ~spl4_50 | spl4_51 | ~spl4_13),
% 1.69/0.65    inference(avatar_split_clause,[],[f599,f167,f607,f603])).
% 1.69/0.65  fof(f167,plain,(
% 1.69/0.65    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.69/0.65  fof(f599,plain,(
% 1.69/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.69/0.65    inference(resolution,[],[f229,f169])).
% 1.69/0.65  fof(f169,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.69/0.65    inference(avatar_component_clause,[],[f167])).
% 1.69/0.65  fof(f528,plain,(
% 1.69/0.65    spl4_45 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_27),
% 1.69/0.65    inference(avatar_split_clause,[],[f523,f334,f205,f181,f161,f121,f525])).
% 1.69/0.65  fof(f121,plain,(
% 1.69/0.65    spl4_4 <=> v2_funct_1(sK2)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.69/0.65  fof(f334,plain,(
% 1.69/0.65    spl4_27 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.69/0.65  fof(f523,plain,(
% 1.69/0.65    sK1 = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_27)),
% 1.69/0.65    inference(forward_demodulation,[],[f522,f207])).
% 1.69/0.65  fof(f522,plain,(
% 1.69/0.65    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27)),
% 1.69/0.65    inference(subsumption_resolution,[],[f521,f183])).
% 1.69/0.65  fof(f521,plain,(
% 1.69/0.65    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_27)),
% 1.69/0.65    inference(subsumption_resolution,[],[f520,f163])).
% 1.69/0.65  fof(f520,plain,(
% 1.69/0.65    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_27)),
% 1.69/0.65    inference(subsumption_resolution,[],[f508,f123])).
% 1.69/0.65  fof(f123,plain,(
% 1.69/0.65    v2_funct_1(sK2) | ~spl4_4),
% 1.69/0.65    inference(avatar_component_clause,[],[f121])).
% 1.69/0.65  fof(f508,plain,(
% 1.69/0.65    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_27),
% 1.69/0.65    inference(superposition,[],[f76,f336])).
% 1.69/0.65  fof(f336,plain,(
% 1.69/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_27),
% 1.69/0.65    inference(avatar_component_clause,[],[f334])).
% 1.69/0.65  fof(f76,plain,(
% 1.69/0.65    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f31])).
% 1.69/0.65  fof(f506,plain,(
% 1.69/0.65    spl4_43 | ~spl4_37 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35),
% 1.69/0.65    inference(avatar_split_clause,[],[f501,f412,f146,f141,f136,f116,f453,f503])).
% 1.69/0.65  fof(f412,plain,(
% 1.69/0.65    spl4_35 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.69/0.65  fof(f501,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f500,f148])).
% 1.69/0.65  fof(f500,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f499,f143])).
% 1.69/0.65  fof(f499,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f498,f138])).
% 1.69/0.65  fof(f498,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f436,f118])).
% 1.69/0.65  fof(f436,plain,(
% 1.69/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f435])).
% 1.69/0.65  fof(f435,plain,(
% 1.69/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(superposition,[],[f309,f414])).
% 1.69/0.65  fof(f414,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_35),
% 1.69/0.65    inference(avatar_component_clause,[],[f412])).
% 1.69/0.65  fof(f309,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(forward_demodulation,[],[f71,f95])).
% 1.69/0.65  fof(f71,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f25])).
% 1.69/0.65  fof(f25,plain,(
% 1.69/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.65    inference(flattening,[],[f24])).
% 1.69/0.65  fof(f24,plain,(
% 1.69/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.65    inference(ennf_transformation,[],[f18])).
% 1.69/0.65  fof(f18,axiom,(
% 1.69/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.69/0.65  fof(f497,plain,(
% 1.69/0.65    spl4_42 | ~spl4_37 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35),
% 1.69/0.65    inference(avatar_split_clause,[],[f492,f412,f146,f141,f136,f116,f453,f494])).
% 1.69/0.65  fof(f492,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f491,f148])).
% 1.69/0.65  fof(f491,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f490,f143])).
% 1.69/0.65  fof(f490,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f489,f138])).
% 1.69/0.65  fof(f489,plain,(
% 1.69/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f437,f118])).
% 1.69/0.65  fof(f437,plain,(
% 1.69/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f434])).
% 1.69/0.65  fof(f434,plain,(
% 1.69/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(superposition,[],[f308,f414])).
% 1.69/0.65  fof(f308,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(forward_demodulation,[],[f70,f95])).
% 1.69/0.65  fof(f70,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f25])).
% 1.69/0.65  fof(f488,plain,(
% 1.69/0.65    spl4_36 | ~spl4_7 | ~spl4_35),
% 1.69/0.65    inference(avatar_split_clause,[],[f487,f412,f136,f445])).
% 1.69/0.65  fof(f487,plain,(
% 1.69/0.65    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f433,f138])).
% 1.69/0.65  fof(f433,plain,(
% 1.69/0.65    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_35),
% 1.69/0.65    inference(superposition,[],[f99,f414])).
% 1.69/0.65  fof(f99,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.65    inference(cnf_transformation,[],[f52])).
% 1.69/0.65  fof(f52,plain,(
% 1.69/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.65    inference(ennf_transformation,[],[f9])).
% 1.69/0.65  fof(f9,axiom,(
% 1.69/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.69/0.65  fof(f476,plain,(
% 1.69/0.65    ~spl4_37 | spl4_40 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35),
% 1.69/0.65    inference(avatar_split_clause,[],[f471,f412,f146,f141,f136,f473,f453])).
% 1.69/0.65  fof(f471,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f470,f148])).
% 1.69/0.65  fof(f470,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f469,f143])).
% 1.69/0.65  fof(f469,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f440,f138])).
% 1.69/0.65  fof(f440,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f430])).
% 1.69/0.65  fof(f430,plain,(
% 1.69/0.65    sK0 != sK0 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(superposition,[],[f74,f414])).
% 1.69/0.65  fof(f74,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f27])).
% 1.69/0.65  fof(f27,plain,(
% 1.69/0.65    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.65    inference(flattening,[],[f26])).
% 1.69/0.65  fof(f26,plain,(
% 1.69/0.65    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.65    inference(ennf_transformation,[],[f17])).
% 1.69/0.65  fof(f17,axiom,(
% 1.69/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.69/0.65  fof(f460,plain,(
% 1.69/0.65    ~spl4_37 | spl4_38 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35),
% 1.69/0.65    inference(avatar_split_clause,[],[f451,f412,f146,f141,f136,f457,f453])).
% 1.69/0.65  fof(f451,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f450,f148])).
% 1.69/0.65  fof(f450,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f449,f143])).
% 1.69/0.65  fof(f449,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_35)),
% 1.69/0.65    inference(subsumption_resolution,[],[f442,f138])).
% 1.69/0.65  fof(f442,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f428])).
% 1.69/0.65  fof(f428,plain,(
% 1.69/0.65    sK0 != sK0 | v1_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_35),
% 1.69/0.65    inference(superposition,[],[f72,f414])).
% 1.69/0.65  fof(f72,plain,(
% 1.69/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f27])).
% 1.69/0.65  fof(f415,plain,(
% 1.69/0.65    spl4_35 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.69/0.65    inference(avatar_split_clause,[],[f410,f167,f161,f156,f151,f146,f141,f136,f412])).
% 1.69/0.65  fof(f410,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f409,f148])).
% 1.69/0.65  fof(f409,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f408,f143])).
% 1.69/0.65  fof(f408,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f407,f138])).
% 1.69/0.65  fof(f407,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f406,f163])).
% 1.69/0.65  fof(f406,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f405,f158])).
% 1.69/0.65  fof(f405,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f402,f153])).
% 1.69/0.65  fof(f402,plain,(
% 1.69/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.69/0.65    inference(resolution,[],[f401,f169])).
% 1.69/0.65  fof(f401,plain,(
% 1.69/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(forward_demodulation,[],[f93,f95])).
% 1.69/0.65  fof(f93,plain,(
% 1.69/0.65    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f47])).
% 1.69/0.65  fof(f47,plain,(
% 1.69/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.65    inference(flattening,[],[f46])).
% 1.69/0.65  fof(f46,plain,(
% 1.69/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.65    inference(ennf_transformation,[],[f15])).
% 1.69/0.65  fof(f15,axiom,(
% 1.69/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.69/0.65  fof(f398,plain,(
% 1.69/0.65    ~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_30),
% 1.69/0.65    inference(avatar_contradiction_clause,[],[f397])).
% 1.69/0.65  fof(f397,plain,(
% 1.69/0.65    $false | (~spl4_4 | ~spl4_12 | ~spl4_15 | spl4_30)),
% 1.69/0.65    inference(subsumption_resolution,[],[f396,f183])).
% 1.69/0.65  fof(f396,plain,(
% 1.69/0.65    ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | spl4_30)),
% 1.69/0.65    inference(subsumption_resolution,[],[f395,f163])).
% 1.69/0.65  fof(f395,plain,(
% 1.69/0.65    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | spl4_30)),
% 1.69/0.65    inference(subsumption_resolution,[],[f393,f123])).
% 1.69/0.65  fof(f393,plain,(
% 1.69/0.65    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_30),
% 1.69/0.65    inference(resolution,[],[f366,f85])).
% 1.69/0.65  fof(f85,plain,(
% 1.69/0.65    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f39])).
% 1.69/0.65  fof(f39,plain,(
% 1.69/0.65    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.65    inference(flattening,[],[f38])).
% 1.69/0.65  fof(f38,plain,(
% 1.69/0.65    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f2])).
% 1.69/0.65  fof(f2,axiom,(
% 1.69/0.65    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.69/0.65  fof(f366,plain,(
% 1.69/0.65    ~v2_funct_1(k2_funct_1(sK2)) | spl4_30),
% 1.69/0.65    inference(avatar_component_clause,[],[f364])).
% 1.69/0.65  fof(f364,plain,(
% 1.69/0.65    spl4_30 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.69/0.65  fof(f389,plain,(
% 1.69/0.65    ~spl4_30 | spl4_34 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19 | ~spl4_24 | ~spl4_26),
% 1.69/0.65    inference(avatar_split_clause,[],[f384,f320,f286,f240,f181,f161,f121,f386,f364])).
% 1.69/0.65  fof(f240,plain,(
% 1.69/0.65    spl4_19 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.69/0.65  fof(f286,plain,(
% 1.69/0.65    spl4_24 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.69/0.65  fof(f320,plain,(
% 1.69/0.65    spl4_26 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.69/0.65  fof(f384,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f383,f183])).
% 1.69/0.65  fof(f383,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f382,f163])).
% 1.69/0.65  fof(f382,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_19 | ~spl4_24 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f381,f288])).
% 1.69/0.65  fof(f288,plain,(
% 1.69/0.65    v1_relat_1(k2_funct_1(sK2)) | ~spl4_24),
% 1.69/0.65    inference(avatar_component_clause,[],[f286])).
% 1.69/0.65  fof(f381,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_19 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f380,f242])).
% 1.69/0.65  fof(f242,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK2)) | ~spl4_19),
% 1.69/0.65    inference(avatar_component_clause,[],[f240])).
% 1.69/0.65  fof(f380,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f341,f123])).
% 1.69/0.65  fof(f341,plain,(
% 1.69/0.65    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_26),
% 1.69/0.65    inference(superposition,[],[f90,f322])).
% 1.69/0.65  fof(f322,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_26),
% 1.69/0.65    inference(avatar_component_clause,[],[f320])).
% 1.69/0.65  fof(f90,plain,(
% 1.69/0.65    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f43])).
% 1.69/0.65  fof(f43,plain,(
% 1.69/0.65    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.65    inference(flattening,[],[f42])).
% 1.69/0.65  fof(f42,plain,(
% 1.69/0.65    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.65    inference(ennf_transformation,[],[f3])).
% 1.69/0.65  fof(f3,axiom,(
% 1.69/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.69/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).
% 1.69/0.65  fof(f349,plain,(
% 1.69/0.65    spl4_28 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26),
% 1.69/0.65    inference(avatar_split_clause,[],[f344,f320,f181,f161,f121,f346])).
% 1.69/0.65  fof(f346,plain,(
% 1.69/0.65    spl4_28 <=> k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.69/0.65  fof(f344,plain,(
% 1.69/0.65    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f343,f183])).
% 1.69/0.65  fof(f343,plain,(
% 1.69/0.65    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f342,f163])).
% 1.69/0.65  fof(f342,plain,(
% 1.69/0.65    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_26)),
% 1.69/0.65    inference(subsumption_resolution,[],[f338,f123])).
% 1.69/0.65  fof(f338,plain,(
% 1.69/0.65    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_26),
% 1.69/0.65    inference(superposition,[],[f79,f322])).
% 1.69/0.65  fof(f79,plain,(
% 1.69/0.65    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.65    inference(cnf_transformation,[],[f33])).
% 1.69/0.65  fof(f337,plain,(
% 1.69/0.65    spl4_27 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.69/0.65    inference(avatar_split_clause,[],[f332,f161,f156,f151,f131,f121,f111,f334])).
% 1.69/0.65  fof(f111,plain,(
% 1.69/0.65    spl4_2 <=> k1_xboole_0 = sK1),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.69/0.65  fof(f332,plain,(
% 1.69/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.69/0.65    inference(subsumption_resolution,[],[f331,f163])).
% 1.69/0.65  fof(f331,plain,(
% 1.69/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.69/0.65    inference(subsumption_resolution,[],[f330,f158])).
% 1.69/0.65  fof(f330,plain,(
% 1.69/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.69/0.65    inference(subsumption_resolution,[],[f329,f153])).
% 1.69/0.65  fof(f329,plain,(
% 1.69/0.65    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.69/0.65    inference(subsumption_resolution,[],[f328,f123])).
% 1.69/0.65  fof(f328,plain,(
% 1.69/0.65    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.69/0.65    inference(subsumption_resolution,[],[f327,f113])).
% 1.69/0.65  fof(f113,plain,(
% 1.69/0.65    k1_xboole_0 != sK1 | spl4_2),
% 1.69/0.65    inference(avatar_component_clause,[],[f111])).
% 1.69/0.65  fof(f327,plain,(
% 1.69/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f324])).
% 1.69/0.65  fof(f324,plain,(
% 1.69/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(superposition,[],[f309,f133])).
% 1.69/0.65  fof(f323,plain,(
% 1.69/0.65    spl4_26 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.69/0.65    inference(avatar_split_clause,[],[f318,f161,f156,f151,f131,f121,f111,f320])).
% 1.69/0.65  fof(f318,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.69/0.65    inference(subsumption_resolution,[],[f317,f163])).
% 1.69/0.65  fof(f317,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.69/0.65    inference(subsumption_resolution,[],[f316,f158])).
% 1.69/0.65  fof(f316,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.69/0.65    inference(subsumption_resolution,[],[f315,f153])).
% 1.69/0.65  fof(f315,plain,(
% 1.69/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.69/0.65    inference(subsumption_resolution,[],[f314,f123])).
% 1.69/0.65  fof(f314,plain,(
% 1.69/0.65    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.69/0.65    inference(subsumption_resolution,[],[f313,f113])).
% 1.69/0.65  fof(f313,plain,(
% 1.69/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f310])).
% 1.69/0.65  fof(f310,plain,(
% 1.69/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(superposition,[],[f308,f133])).
% 1.69/0.65  fof(f301,plain,(
% 1.69/0.65    spl4_25 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.69/0.65    inference(avatar_split_clause,[],[f296,f167,f161,f151,f146,f136,f298])).
% 1.69/0.65  fof(f296,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f295,f163])).
% 1.69/0.65  fof(f295,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f294,f153])).
% 1.69/0.65  fof(f294,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f293,f148])).
% 1.69/0.65  fof(f293,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.69/0.65    inference(subsumption_resolution,[],[f290,f138])).
% 1.69/0.65  fof(f290,plain,(
% 1.69/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.69/0.65    inference(superposition,[],[f169,f98])).
% 1.69/0.65  fof(f289,plain,(
% 1.69/0.65    spl4_24 | ~spl4_21),
% 1.69/0.65    inference(avatar_split_clause,[],[f273,f266,f286])).
% 1.69/0.65  fof(f266,plain,(
% 1.69/0.65    spl4_21 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.69/0.65  fof(f273,plain,(
% 1.69/0.65    v1_relat_1(k2_funct_1(sK2)) | ~spl4_21),
% 1.69/0.65    inference(resolution,[],[f268,f100])).
% 1.69/0.65  fof(f268,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 1.69/0.65    inference(avatar_component_clause,[],[f266])).
% 1.69/0.65  fof(f279,plain,(
% 1.69/0.65    ~spl4_22 | spl4_1 | ~spl4_7 | ~spl4_21),
% 1.69/0.65    inference(avatar_split_clause,[],[f274,f266,f136,f106,f276])).
% 1.69/0.65  fof(f276,plain,(
% 1.69/0.65    spl4_22 <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.69/0.65  fof(f106,plain,(
% 1.69/0.65    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.69/0.65  fof(f274,plain,(
% 1.69/0.65    ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | (spl4_1 | ~spl4_7 | ~spl4_21)),
% 1.69/0.65    inference(subsumption_resolution,[],[f270,f108])).
% 1.69/0.65  fof(f108,plain,(
% 1.69/0.65    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.69/0.65    inference(avatar_component_clause,[],[f106])).
% 1.69/0.65  fof(f270,plain,(
% 1.69/0.65    k2_funct_1(sK2) = sK3 | ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),sK3) | (~spl4_7 | ~spl4_21)),
% 1.69/0.65    inference(resolution,[],[f268,f227])).
% 1.69/0.65  fof(f227,plain,(
% 1.69/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK3 = X0 | ~r2_relset_1(sK1,sK0,X0,sK3)) ) | ~spl4_7),
% 1.69/0.65    inference(resolution,[],[f91,f138])).
% 1.69/0.65  fof(f269,plain,(
% 1.69/0.65    spl4_21 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.69/0.65    inference(avatar_split_clause,[],[f264,f161,f156,f151,f131,f121,f266])).
% 1.69/0.65  fof(f264,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.69/0.65    inference(subsumption_resolution,[],[f263,f163])).
% 1.69/0.65  fof(f263,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.69/0.65    inference(subsumption_resolution,[],[f262,f158])).
% 1.69/0.65  fof(f262,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.69/0.65    inference(subsumption_resolution,[],[f261,f153])).
% 1.69/0.65  fof(f261,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 1.69/0.65    inference(subsumption_resolution,[],[f260,f123])).
% 1.69/0.65  fof(f260,plain,(
% 1.69/0.65    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f257])).
% 1.69/0.65  fof(f257,plain,(
% 1.69/0.65    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(superposition,[],[f74,f133])).
% 1.69/0.65  fof(f243,plain,(
% 1.69/0.65    spl4_19 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.69/0.65    inference(avatar_split_clause,[],[f238,f161,f156,f151,f131,f121,f240])).
% 1.69/0.65  fof(f238,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK2)) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.69/0.65    inference(subsumption_resolution,[],[f237,f163])).
% 1.69/0.65  fof(f237,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.69/0.65    inference(subsumption_resolution,[],[f236,f158])).
% 1.69/0.65  fof(f236,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.69/0.65    inference(subsumption_resolution,[],[f235,f153])).
% 1.69/0.65  fof(f235,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 1.69/0.65    inference(subsumption_resolution,[],[f234,f123])).
% 1.69/0.65  fof(f234,plain,(
% 1.69/0.65    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(trivial_inequality_removal,[],[f231])).
% 1.69/0.65  fof(f231,plain,(
% 1.69/0.65    sK1 != sK1 | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.69/0.65    inference(superposition,[],[f72,f133])).
% 1.69/0.65  fof(f210,plain,(
% 1.69/0.65    spl4_18 | ~spl4_6 | ~spl4_10),
% 1.69/0.65    inference(avatar_split_clause,[],[f209,f151,f131,f205])).
% 1.69/0.65  fof(f209,plain,(
% 1.69/0.65    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 1.69/0.65    inference(subsumption_resolution,[],[f202,f153])).
% 1.69/0.65  fof(f202,plain,(
% 1.69/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.69/0.65    inference(superposition,[],[f133,f99])).
% 1.69/0.65  fof(f195,plain,(
% 1.69/0.65    spl4_16 | ~spl4_7),
% 1.69/0.65    inference(avatar_split_clause,[],[f188,f136,f192])).
% 1.69/0.65  fof(f192,plain,(
% 1.69/0.65    spl4_16 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.69/0.65  fof(f188,plain,(
% 1.69/0.65    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_7),
% 1.69/0.65    inference(resolution,[],[f104,f138])).
% 1.69/0.65  fof(f104,plain,(
% 1.69/0.65    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.69/0.65    inference(duplicate_literal_removal,[],[f103])).
% 1.69/0.65  fof(f103,plain,(
% 1.69/0.65    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.65    inference(equality_resolution,[],[f92])).
% 1.69/0.65  fof(f92,plain,(
% 1.69/0.65    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.65    inference(cnf_transformation,[],[f57])).
% 1.69/0.65  fof(f184,plain,(
% 1.69/0.65    spl4_15 | ~spl4_10),
% 1.69/0.65    inference(avatar_split_clause,[],[f173,f151,f181])).
% 1.69/0.65  fof(f173,plain,(
% 1.69/0.65    v1_relat_1(sK2) | ~spl4_10),
% 1.69/0.65    inference(resolution,[],[f100,f153])).
% 1.69/0.65  fof(f179,plain,(
% 1.69/0.65    spl4_14 | ~spl4_7),
% 1.69/0.65    inference(avatar_split_clause,[],[f172,f136,f176])).
% 1.69/0.65  fof(f172,plain,(
% 1.69/0.65    v1_relat_1(sK3) | ~spl4_7),
% 1.69/0.65    inference(resolution,[],[f100,f138])).
% 1.69/0.65  fof(f170,plain,(
% 1.69/0.65    spl4_13 | ~spl4_5),
% 1.69/0.65    inference(avatar_split_clause,[],[f165,f126,f167])).
% 1.69/0.65  fof(f126,plain,(
% 1.69/0.65    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.69/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.69/0.66  fof(f165,plain,(
% 1.69/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.69/0.66    inference(backward_demodulation,[],[f128,f95])).
% 1.69/0.66  fof(f128,plain,(
% 1.69/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.69/0.66    inference(avatar_component_clause,[],[f126])).
% 1.69/0.66  fof(f164,plain,(
% 1.69/0.66    spl4_12),
% 1.69/0.66    inference(avatar_split_clause,[],[f58,f161])).
% 1.69/0.66  fof(f58,plain,(
% 1.69/0.66    v1_funct_1(sK2)),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f56,plain,(
% 1.69/0.66    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.69/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f55,f54])).
% 1.69/0.66  fof(f54,plain,(
% 1.69/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.69/0.66    introduced(choice_axiom,[])).
% 1.69/0.66  fof(f55,plain,(
% 1.69/0.66    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.69/0.66    introduced(choice_axiom,[])).
% 1.69/0.66  fof(f23,plain,(
% 1.69/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.69/0.66    inference(flattening,[],[f22])).
% 1.69/0.66  fof(f22,plain,(
% 1.69/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.69/0.66    inference(ennf_transformation,[],[f20])).
% 1.69/0.66  fof(f20,negated_conjecture,(
% 1.69/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.69/0.66    inference(negated_conjecture,[],[f19])).
% 1.69/0.66  fof(f19,conjecture,(
% 1.69/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.69/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.69/0.66  fof(f159,plain,(
% 1.69/0.66    spl4_11),
% 1.69/0.66    inference(avatar_split_clause,[],[f59,f156])).
% 1.69/0.66  fof(f59,plain,(
% 1.69/0.66    v1_funct_2(sK2,sK0,sK1)),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f154,plain,(
% 1.69/0.66    spl4_10),
% 1.69/0.66    inference(avatar_split_clause,[],[f60,f151])).
% 1.69/0.66  fof(f60,plain,(
% 1.69/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f149,plain,(
% 1.69/0.66    spl4_9),
% 1.69/0.66    inference(avatar_split_clause,[],[f61,f146])).
% 1.69/0.66  fof(f61,plain,(
% 1.69/0.66    v1_funct_1(sK3)),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f144,plain,(
% 1.69/0.66    spl4_8),
% 1.69/0.66    inference(avatar_split_clause,[],[f62,f141])).
% 1.69/0.66  fof(f62,plain,(
% 1.69/0.66    v1_funct_2(sK3,sK1,sK0)),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f139,plain,(
% 1.69/0.66    spl4_7),
% 1.69/0.66    inference(avatar_split_clause,[],[f63,f136])).
% 1.69/0.66  fof(f63,plain,(
% 1.69/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f134,plain,(
% 1.69/0.66    spl4_6),
% 1.69/0.66    inference(avatar_split_clause,[],[f64,f131])).
% 1.69/0.66  fof(f64,plain,(
% 1.69/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f129,plain,(
% 1.69/0.66    spl4_5),
% 1.69/0.66    inference(avatar_split_clause,[],[f65,f126])).
% 1.69/0.66  fof(f65,plain,(
% 1.69/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f124,plain,(
% 1.69/0.66    spl4_4),
% 1.69/0.66    inference(avatar_split_clause,[],[f66,f121])).
% 1.69/0.66  fof(f66,plain,(
% 1.69/0.66    v2_funct_1(sK2)),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f119,plain,(
% 1.69/0.66    ~spl4_3),
% 1.69/0.66    inference(avatar_split_clause,[],[f67,f116])).
% 1.69/0.66  fof(f67,plain,(
% 1.69/0.66    k1_xboole_0 != sK0),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f114,plain,(
% 1.69/0.66    ~spl4_2),
% 1.69/0.66    inference(avatar_split_clause,[],[f68,f111])).
% 1.69/0.66  fof(f68,plain,(
% 1.69/0.66    k1_xboole_0 != sK1),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  fof(f109,plain,(
% 1.69/0.66    ~spl4_1),
% 1.69/0.66    inference(avatar_split_clause,[],[f69,f106])).
% 1.69/0.66  fof(f69,plain,(
% 1.69/0.66    k2_funct_1(sK2) != sK3),
% 1.69/0.66    inference(cnf_transformation,[],[f56])).
% 1.69/0.66  % SZS output end Proof for theBenchmark
% 1.69/0.66  % (13539)------------------------------
% 1.69/0.66  % (13539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.66  % (13539)Termination reason: Refutation
% 1.69/0.66  
% 1.69/0.66  % (13539)Memory used [KB]: 7291
% 1.69/0.66  % (13539)Time elapsed: 0.228 s
% 1.69/0.66  % (13539)------------------------------
% 1.69/0.66  % (13539)------------------------------
% 1.69/0.66  % (13517)Success in time 0.291 s
%------------------------------------------------------------------------------
