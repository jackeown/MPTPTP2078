%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:29 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  453 (2205 expanded)
%              Number of leaves         :  100 ( 983 expanded)
%              Depth                    :   14
%              Number of atoms          : 2013 (10096 expanded)
%              Number of equality atoms :  264 (1458 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f185,f190,f198,f203,f210,f215,f225,f234,f297,f310,f320,f327,f336,f347,f354,f359,f373,f378,f401,f422,f427,f440,f451,f461,f469,f504,f513,f524,f529,f534,f539,f557,f565,f576,f583,f596,f609,f615,f625,f633,f644,f651,f654,f661,f669,f682,f697,f704,f715,f735,f743,f773,f799,f888,f893,f898,f903,f1034,f1039,f1044,f1069,f1086,f1098,f1115,f1129,f1151,f1155,f1159,f1161])).

fof(f1161,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_34
    | ~ spl7_43
    | ~ spl7_45
    | ~ spl7_64
    | ~ spl7_68
    | ~ spl7_75 ),
    inference(avatar_contradiction_clause,[],[f1160])).

fof(f1160,plain,
    ( $false
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_34
    | ~ spl7_43
    | ~ spl7_45
    | ~ spl7_64
    | ~ spl7_68
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f1149,f1146])).

fof(f1146,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_34
    | ~ spl7_43
    | ~ spl7_45
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1145,f555])).

fof(f555,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl7_45
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1145,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_34
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1144,f224])).

fof(f224,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_20
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f1144,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_34
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1143,f300])).

fof(f300,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f154,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f154,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1143,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_34
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1130,f403])).

fof(f403,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f139,f174,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f174,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_13
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f139,plain,
    ( v1_funct_1(sK5)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1130,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_34
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f114,f119,f124,f134,f129,f139,f149,f154,f159,f164,f169,f174,f533,f892,f431,f1038,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f1038,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f1036,plain,
    ( spl7_68
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f431,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl7_34
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f892,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f890])).

fof(f890,plain,
    ( spl7_64
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f533,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl7_43
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f169,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl7_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f164,plain,
    ( v1_funct_2(sK5,sK3,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_11
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f159,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_10
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f134,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f124,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f114,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1149,plain,
    ( k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f1148])).

fof(f1148,plain,
    ( spl7_75
  <=> k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1159,plain,
    ( ~ spl7_5
    | ~ spl7_12
    | ~ spl7_47
    | spl7_75 ),
    inference(avatar_contradiction_clause,[],[f1158])).

fof(f1158,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_47
    | spl7_75 ),
    inference(subsumption_resolution,[],[f1157,f134])).

fof(f1157,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl7_12
    | ~ spl7_47
    | spl7_75 ),
    inference(subsumption_resolution,[],[f1156,f169])).

fof(f1156,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ spl7_47
    | spl7_75 ),
    inference(subsumption_resolution,[],[f1153,f575])).

fof(f575,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl7_47
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1153,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | spl7_75 ),
    inference(superposition,[],[f1150,f99])).

fof(f1150,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl7_75 ),
    inference(avatar_component_clause,[],[f1148])).

fof(f1155,plain,
    ( ~ spl7_5
    | ~ spl7_12
    | ~ spl7_47
    | spl7_75 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_47
    | spl7_75 ),
    inference(subsumption_resolution,[],[f1152,f575])).

fof(f1152,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_12
    | spl7_75 ),
    inference(superposition,[],[f1150,f402])).

fof(f402,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl7_5
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f134,f169,f99])).

fof(f1151,plain,
    ( ~ spl7_75
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_35
    | ~ spl7_43
    | ~ spl7_45
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f1142,f1036,f890,f554,f531,f433,f222,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f112,f1148])).

fof(f433,plain,
    ( spl7_35
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1142,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_35
    | ~ spl7_43
    | ~ spl7_45
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1141,f555])).

fof(f1141,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20
    | spl7_35
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1140,f224])).

fof(f1140,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_35
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1139,f300])).

fof(f1139,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_35
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f1131,f403])).

fof(f1131,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_35
    | ~ spl7_43
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f114,f119,f124,f134,f129,f139,f149,f154,f159,f164,f169,f174,f533,f892,f435,f1038,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f435,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl7_35 ),
    inference(avatar_component_clause,[],[f433])).

fof(f1129,plain,
    ( spl7_74
    | spl7_2
    | ~ spl7_42
    | ~ spl7_63
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f1087,f1031,f885,f526,f117,f1126])).

fof(f1126,plain,
    ( spl7_74
  <=> v1_partfun1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f526,plain,
    ( spl7_42
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f885,plain,
    ( spl7_63
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f1031,plain,
    ( spl7_67
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f1087,plain,
    ( v1_partfun1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2))
    | spl7_2
    | ~ spl7_42
    | ~ spl7_63
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f119,f528,f887,f1033,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f1033,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1)))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f1031])).

fof(f887,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1)
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f885])).

fof(f528,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f526])).

fof(f1115,plain,
    ( spl7_73
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f1047,f900,f1112])).

fof(f1112,plain,
    ( spl7_73
  <=> v4_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f900,plain,
    ( spl7_66
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1047,plain,
    ( v4_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2))
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f902,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f902,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f900])).

fof(f1098,plain,
    ( spl7_72
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f1088,f1031,f1095])).

fof(f1095,plain,
    ( spl7_72
  <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f1088,plain,
    ( v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f1033,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1086,plain,
    ( spl7_71
    | spl7_2
    | ~ spl7_41
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f1045,f900,f796,f521,f117,f1083])).

fof(f1083,plain,
    ( spl7_71
  <=> v1_partfun1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f521,plain,
    ( spl7_41
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f796,plain,
    ( spl7_62
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1045,plain,
    ( v1_partfun1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2))
    | spl7_2
    | ~ spl7_41
    | ~ spl7_62
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f119,f523,f798,f902,f87])).

fof(f798,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f796])).

fof(f523,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1069,plain,
    ( spl7_70
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f1046,f900,f1066])).

fof(f1066,plain,
    ( spl7_70
  <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f1046,plain,
    ( v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f902,f97])).

fof(f1044,plain,
    ( spl7_69
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f547,f172,f162,f152,f137,f127,f117,f1041])).

fof(f1041,plain,
    ( spl7_69
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f547,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f129,f139,f129,f139,f154,f154,f164,f174,f164,f174,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f102,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f1039,plain,
    ( spl7_68
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f546,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f1036])).

fof(f546,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f124,f134,f129,f139,f149,f154,f159,f169,f164,f174,f108])).

fof(f1034,plain,
    ( spl7_67
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f545,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f1031])).

fof(f545,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1)))
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f129,f139,f124,f134,f154,f149,f164,f174,f159,f169,f108])).

fof(f903,plain,
    ( spl7_66
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f544,f167,f157,f147,f132,f122,f117,f900])).

fof(f544,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f119,f124,f134,f124,f134,f149,f149,f159,f169,f159,f169,f108])).

fof(f898,plain,
    ( spl7_65
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f543,f172,f162,f152,f137,f127,f117,f895])).

fof(f895,plain,
    ( spl7_65
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f543,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f129,f139,f129,f139,f154,f154,f164,f174,f164,f174,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f101,f80])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f893,plain,
    ( spl7_64
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f542,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f890])).

fof(f542,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f124,f134,f129,f139,f149,f154,f159,f169,f164,f174,f109])).

fof(f888,plain,
    ( spl7_63
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f541,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f885])).

fof(f541,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1)
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f129,f139,f124,f134,f154,f149,f164,f174,f159,f169,f109])).

fof(f799,plain,
    ( spl7_62
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f540,f167,f157,f147,f132,f122,f117,f796])).

fof(f540,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f119,f124,f134,f124,f134,f149,f149,f159,f169,f159,f169,f109])).

fof(f773,plain,
    ( spl7_61
    | ~ spl7_22
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f692,f458,f294,f770])).

fof(f770,plain,
    ( spl7_61
  <=> k1_xboole_0 = k7_relat_1(sK6(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f294,plain,
    ( spl7_22
  <=> k1_xboole_0 = k7_relat_1(sK6(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f458,plain,
    ( spl7_37
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f692,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(sK3),k1_xboole_0)
    | ~ spl7_22
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f687,f296])).

fof(f296,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(sK3),sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f294])).

fof(f687,plain,
    ( k7_relat_1(sK6(sK3),sK2) = k7_relat_1(sK6(sK3),k1_xboole_0)
    | ~ spl7_37 ),
    inference(superposition,[],[f277,f460])).

fof(f460,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK2)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f458])).

fof(f277,plain,(
    ! [X0,X1] : k7_relat_1(sK6(X0),X1) = k7_relat_1(sK6(X0),k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f252,f276])).

fof(f276,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(sK6(X0),X1)) ),
    inference(backward_demodulation,[],[f238,f270])).

fof(f270,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f82,f83,f85,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f85,plain,(
    ! [X0] : v1_partfun1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_partfun1(sK6(X0),X0)
      & v1_funct_1(sK6(X0))
      & v4_relat_1(sK6(X0),X0)
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v1_partfun1(sK6(X0),X0)
        & v1_funct_1(sK6(X0))
        & v4_relat_1(sK6(X0),X0)
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(f83,plain,(
    ! [X0] : v4_relat_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f238,plain,(
    ! [X0,X1] : k3_xboole_0(k1_relat_1(sK6(X0)),X1) = k1_relat_1(k7_relat_1(sK6(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f82,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f252,plain,(
    ! [X0,X1] : k7_relat_1(sK6(X0),X1) = k7_relat_1(sK6(X0),k1_relat_1(k7_relat_1(sK6(X0),X1))) ),
    inference(forward_demodulation,[],[f246,f238])).

fof(f246,plain,(
    ! [X0,X1] : k7_relat_1(sK6(X0),X1) = k7_relat_1(sK6(X0),k3_xboole_0(k1_relat_1(sK6(X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f82,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f743,plain,
    ( spl7_60
    | ~ spl7_59 ),
    inference(avatar_split_clause,[],[f736,f732,f740])).

fof(f740,plain,
    ( spl7_60
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f732,plain,
    ( spl7_59
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f736,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_59 ),
    inference(unit_resulting_resolution,[],[f734,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f734,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f732])).

fof(f735,plain,
    ( spl7_59
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f730,f712,f333,f317,f732])).

fof(f317,plain,
    ( spl7_25
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f333,plain,
    ( spl7_27
  <=> k1_xboole_0 = sK6(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f712,plain,
    ( spl7_58
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f730,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f729,f318])).

fof(f318,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f317])).

fof(f729,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_27
    | ~ spl7_58 ),
    inference(superposition,[],[f337,f714])).

fof(f714,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f712])).

fof(f337,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl7_27 ),
    inference(superposition,[],[f276,f335])).

fof(f335,plain,
    ( k1_xboole_0 = sK6(k1_xboole_0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f333])).

fof(f715,plain,
    ( spl7_58
    | ~ spl7_27
    | ~ spl7_51
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f690,f622,f612,f333,f712])).

fof(f612,plain,
    ( spl7_51
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f622,plain,
    ( spl7_52
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f690,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_27
    | ~ spl7_51
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f689,f614])).

fof(f614,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f612])).

fof(f689,plain,
    ( k7_relat_1(k1_xboole_0,sK2) = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_27
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f684,f335])).

fof(f684,plain,
    ( k7_relat_1(sK6(k1_xboole_0),sK2) = k7_relat_1(sK6(k1_xboole_0),k1_xboole_0)
    | ~ spl7_52 ),
    inference(superposition,[],[f277,f624])).

fof(f624,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f622])).

fof(f704,plain,
    ( spl7_50
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f695,f679,f333,f317,f606])).

fof(f606,plain,
    ( spl7_50
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f679,plain,
    ( spl7_57
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f695,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK3)
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_57 ),
    inference(forward_demodulation,[],[f694,f318])).

fof(f694,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK3)
    | ~ spl7_27
    | ~ spl7_57 ),
    inference(superposition,[],[f337,f681])).

fof(f681,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f679])).

fof(f697,plain,
    ( ~ spl7_25
    | ~ spl7_27
    | spl7_50
    | ~ spl7_57 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl7_25
    | ~ spl7_27
    | spl7_50
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f695,f608])).

fof(f608,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK3)
    | spl7_50 ),
    inference(avatar_component_clause,[],[f606])).

fof(f682,plain,
    ( spl7_57
    | ~ spl7_27
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f676,f666,f333,f679])).

fof(f666,plain,
    ( spl7_56
  <=> r1_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f676,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)
    | ~ spl7_27
    | ~ spl7_56 ),
    inference(forward_demodulation,[],[f671,f335])).

fof(f671,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(k1_xboole_0),sK3)
    | ~ spl7_56 ),
    inference(unit_resulting_resolution,[],[f668,f282])).

fof(f282,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X5,X4)
      | k1_xboole_0 = k7_relat_1(sK6(X4),X5) ) ),
    inference(subsumption_resolution,[],[f280,f82])).

fof(f280,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X5,X4)
      | k1_xboole_0 = k7_relat_1(sK6(X4),X5)
      | ~ v1_relat_1(sK6(X4)) ) ),
    inference(superposition,[],[f79,f270])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f668,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f666])).

fof(f669,plain,
    ( spl7_56
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f662,f658,f666])).

fof(f658,plain,
    ( spl7_55
  <=> k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f662,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f660,f95])).

fof(f660,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f658])).

fof(f661,plain,
    ( spl7_55
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_25
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f656,f554,f375,f317,f207,f187,f658])).

fof(f187,plain,
    ( spl7_15
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f207,plain,
    ( spl7_18
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f375,plain,
    ( spl7_30
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f656,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_25
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f655,f318])).

fof(f655,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(superposition,[],[f392,f555])).

fof(f392,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0)
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30 ),
    inference(backward_demodulation,[],[f237,f388])).

fof(f388,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f189,f209,f377,f92])).

fof(f377,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f375])).

fof(f209,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f207])).

fof(f189,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f237,plain,
    ( ! [X0] : k3_xboole_0(k1_relat_1(sK5),X0) = k1_relat_1(k7_relat_1(sK5,X0))
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f189,f88])).

fof(f654,plain,
    ( spl7_45
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_37
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f649,f510,f458,f375,f207,f187,f554])).

fof(f510,plain,
    ( spl7_40
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f649,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_37
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f647,f512])).

fof(f512,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f510])).

fof(f647,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2)
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_37 ),
    inference(superposition,[],[f395,f460])).

fof(f395,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0))
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30 ),
    inference(backward_demodulation,[],[f253,f392])).

fof(f253,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0)))
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f245,f237])).

fof(f245,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0))
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f189,f89])).

fof(f651,plain,
    ( ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_37
    | ~ spl7_40
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_37
    | ~ spl7_40
    | spl7_45 ),
    inference(subsumption_resolution,[],[f649,f556])).

fof(f556,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f554])).

fof(f644,plain,
    ( spl7_54
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f635,f630,f641])).

fof(f641,plain,
    ( spl7_54
  <=> k1_xboole_0 = k7_relat_1(sK6(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f630,plain,
    ( spl7_53
  <=> r1_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f635,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(sK2),k1_xboole_0)
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f632,f282])).

fof(f632,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f630])).

fof(f633,plain,
    ( spl7_53
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f626,f622,f630])).

fof(f626,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f624,f95])).

fof(f625,plain,
    ( spl7_52
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f620,f612,f333,f317,f622])).

fof(f620,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_51 ),
    inference(forward_demodulation,[],[f619,f318])).

fof(f619,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_27
    | ~ spl7_51 ),
    inference(superposition,[],[f337,f614])).

fof(f615,plain,
    ( spl7_51
    | ~ spl7_27
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f603,f593,f333,f612])).

fof(f593,plain,
    ( spl7_49
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f603,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)
    | ~ spl7_27
    | ~ spl7_49 ),
    inference(forward_demodulation,[],[f598,f335])).

fof(f598,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(k1_xboole_0),sK2)
    | ~ spl7_49 ),
    inference(unit_resulting_resolution,[],[f595,f282])).

fof(f595,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f593])).

fof(f609,plain,
    ( ~ spl7_50
    | spl7_46 ),
    inference(avatar_split_clause,[],[f571,f562,f606])).

fof(f562,plain,
    ( spl7_46
  <=> r1_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f571,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK3)
    | spl7_46 ),
    inference(unit_resulting_resolution,[],[f564,f95])).

fof(f564,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK3)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f562])).

fof(f596,plain,
    ( spl7_49
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f584,f580,f593])).

fof(f580,plain,
    ( spl7_48
  <=> k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f584,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f582,f95])).

fof(f582,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f580])).

fof(f583,plain,
    ( spl7_48
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_25
    | ~ spl7_29
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f578,f573,f370,f317,f200,f182,f580])).

fof(f182,plain,
    ( spl7_14
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f200,plain,
    ( spl7_17
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f370,plain,
    ( spl7_29
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f578,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_25
    | ~ spl7_29
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f577,f318])).

fof(f577,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_29
    | ~ spl7_47 ),
    inference(superposition,[],[f383,f575])).

fof(f383,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(sK2,X0)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f236,f379])).

fof(f379,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f184,f202,f372,f92])).

fof(f372,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f370])).

fof(f202,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f184,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f236,plain,
    ( ! [X0] : k3_xboole_0(k1_relat_1(sK4),X0) = k1_relat_1(k7_relat_1(sK4,X0))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f184,f88])).

fof(f576,plain,
    ( spl7_47
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_29
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f550,f501,f370,f222,f200,f182,f573])).

fof(f501,plain,
    ( spl7_39
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f550,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_29
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f548,f503])).

fof(f503,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f501])).

fof(f548,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK4,sK3)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(superposition,[],[f386,f224])).

fof(f386,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f254,f383])).

fof(f254,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0)))
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f244,f236])).

fof(f244,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f184,f89])).

fof(f565,plain,
    ( ~ spl7_46
    | ~ spl7_15
    | ~ spl7_33
    | spl7_45 ),
    inference(avatar_split_clause,[],[f559,f554,f424,f187,f562])).

fof(f424,plain,
    ( spl7_33
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f559,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl7_15
    | ~ spl7_33
    | spl7_45 ),
    inference(unit_resulting_resolution,[],[f556,f450])).

fof(f450,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl7_15
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f448,f189])).

fof(f448,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2)
        | ~ v1_relat_1(sK5) )
    | ~ spl7_33 ),
    inference(superposition,[],[f79,f426])).

fof(f426,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f424])).

fof(f557,plain,
    ( ~ spl7_45
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_29
    | spl7_36
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f551,f501,f437,f370,f222,f200,f182,f554])).

fof(f437,plain,
    ( spl7_36
  <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f551,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_29
    | spl7_36
    | ~ spl7_39 ),
    inference(backward_demodulation,[],[f439,f550])).

fof(f439,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl7_36 ),
    inference(avatar_component_clause,[],[f437])).

fof(f539,plain,
    ( spl7_44
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f519,f172,f162,f152,f137,f127,f117,f536])).

fof(f536,plain,
    ( spl7_44
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f519,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f129,f139,f129,f139,f154,f154,f164,f174,f164,f174,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f534,plain,
    ( spl7_43
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f518,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f531])).

fof(f518,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f124,f134,f129,f139,f149,f154,f159,f169,f164,f174,f110])).

fof(f529,plain,
    ( spl7_42
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f517,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f526])).

fof(f517,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f129,f139,f124,f134,f154,f149,f164,f174,f159,f169,f110])).

fof(f524,plain,
    ( spl7_41
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f516,f167,f157,f147,f132,f122,f117,f521])).

fof(f516,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f119,f124,f134,f124,f134,f149,f149,f159,f169,f159,f169,f110])).

fof(f513,plain,
    ( spl7_40
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f507,f424,f212,f187,f510])).

fof(f212,plain,
    ( spl7_19
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f507,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f214,f450])).

fof(f214,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f504,plain,
    ( spl7_39
    | ~ spl7_14
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f497,f419,f313,f182,f501])).

fof(f313,plain,
    ( spl7_24
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f419,plain,
    ( spl7_32
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f497,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl7_14
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f315,f445])).

fof(f445,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X2) )
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f443,f184])).

fof(f443,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X2)
        | ~ v1_relat_1(sK4) )
    | ~ spl7_32 ),
    inference(superposition,[],[f79,f421])).

fof(f421,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f419])).

fof(f315,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f313])).

fof(f469,plain,
    ( spl7_38
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f411,f313,f466])).

fof(f466,plain,
    ( spl7_38
  <=> k1_xboole_0 = k7_relat_1(sK6(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f411,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(sK2),sK3)
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f315,f282])).

fof(f461,plain,
    ( spl7_37
    | ~ spl7_23
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f351,f333,f307,f458])).

fof(f307,plain,
    ( spl7_23
  <=> k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f351,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK2)
    | ~ spl7_23
    | ~ spl7_27 ),
    inference(backward_demodulation,[],[f309,f338])).

fof(f338,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_27 ),
    inference(superposition,[],[f270,f335])).

fof(f309,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,sK2)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f307])).

fof(f451,plain,
    ( spl7_25
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f338,f333,f317])).

fof(f440,plain,
    ( ~ spl7_34
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f406,f222,f172,f167,f152,f137,f132,f437,f433,f429])).

fof(f406,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f405,f402])).

fof(f405,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f305,f403])).

fof(f305,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f304,f224])).

fof(f304,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f74,f300])).

fof(f74,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
      | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X5,X3,X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                    & v1_funct_2(X4,X2,X1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(sK0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                      & v1_funct_2(X5,X3,sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                  & v1_funct_2(X4,X2,sK1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                    & v1_funct_2(X5,X3,sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                & v1_funct_2(X4,X2,sK1)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                    | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                  & v1_funct_2(X5,X3,sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
              & v1_funct_2(X4,sK2,sK1)
              & v1_funct_1(X4) )
          & r1_subset_1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                  | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                & v1_funct_2(X5,X3,sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
            & v1_funct_2(X4,sK2,sK1)
            & v1_funct_1(X4) )
        & r1_subset_1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
                | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
                | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_2(X5,sK3,sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X4,sK2,sK1)
          & v1_funct_1(X4) )
      & r1_subset_1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
              | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
              | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_2(X5,sK3,sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X4,sK2,sK1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
            | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
            | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_2(X5,sK3,sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
          | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
          | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_2(X5,sK3,sK1)
        & v1_funct_1(X5) )
   => ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
        | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
        | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_2(sK5,sK3,sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f427,plain,
    ( spl7_33
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f388,f375,f207,f187,f424])).

fof(f422,plain,
    ( spl7_32
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f379,f370,f200,f182,f419])).

fof(f401,plain,
    ( spl7_31
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f339,f333,f398])).

fof(f398,plain,
    ( spl7_31
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f339,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_27 ),
    inference(superposition,[],[f85,f335])).

fof(f378,plain,
    ( spl7_30
    | spl7_2
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f361,f172,f162,f137,f117,f375])).

fof(f361,plain,
    ( v1_partfun1(sK5,sK3)
    | spl7_2
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f119,f139,f164,f174,f87])).

fof(f373,plain,
    ( spl7_29
    | spl7_2
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f360,f167,f157,f132,f117,f370])).

fof(f360,plain,
    ( v1_partfun1(sK4,sK2)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f119,f134,f159,f169,f87])).

fof(f359,plain,
    ( spl7_28
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f341,f333,f356])).

fof(f356,plain,
    ( spl7_28
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f341,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_27 ),
    inference(superposition,[],[f84,f335])).

fof(f84,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f354,plain,
    ( spl7_3
    | spl7_4
    | ~ spl7_24
    | spl7_26 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl7_3
    | spl7_4
    | ~ spl7_24
    | spl7_26 ),
    inference(subsumption_resolution,[],[f315,f349])).

fof(f349,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | spl7_3
    | spl7_4
    | spl7_26 ),
    inference(subsumption_resolution,[],[f348,f129])).

fof(f348,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | spl7_3
    | spl7_26 ),
    inference(subsumption_resolution,[],[f331,f124])).

fof(f331,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK3)
    | spl7_26 ),
    inference(resolution,[],[f326,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f326,plain,
    ( ~ r1_subset_1(sK3,sK2)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl7_26
  <=> r1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f347,plain,
    ( spl7_25
    | ~ spl7_27 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl7_25
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f338,f319])).

fof(f319,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f317])).

fof(f336,plain,(
    spl7_27 ),
    inference(avatar_split_clause,[],[f328,f333])).

fof(f328,plain,(
    k1_xboole_0 = sK6(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f82,f84,f83,f85,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).

fof(f327,plain,
    ( ~ spl7_26
    | spl7_3
    | spl7_4
    | spl7_24 ),
    inference(avatar_split_clause,[],[f321,f313,f127,f122,f324])).

fof(f321,plain,
    ( ~ r1_subset_1(sK3,sK2)
    | spl7_3
    | spl7_4
    | spl7_24 ),
    inference(unit_resulting_resolution,[],[f129,f124,f314,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f314,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f313])).

fof(f320,plain,
    ( spl7_24
    | ~ spl7_25
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f311,f307,f317,f313])).

fof(f311,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_xboole_0(sK3,sK2)
    | ~ spl7_23 ),
    inference(superposition,[],[f95,f309])).

fof(f310,plain,
    ( spl7_23
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f298,f294,f307])).

fof(f298,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,sK2)
    | ~ spl7_22 ),
    inference(superposition,[],[f276,f296])).

fof(f297,plain,
    ( spl7_22
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f291,f212,f294])).

fof(f291,plain,
    ( k1_xboole_0 = k7_relat_1(sK6(sK3),sK2)
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f214,f282])).

fof(f234,plain,
    ( spl7_21
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f229,f195,f231])).

fof(f231,plain,
    ( spl7_21
  <=> v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f195,plain,
    ( spl7_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f229,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f197,f193,f107])).

fof(f107,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f193,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f75,f98])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f197,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f225,plain,
    ( spl7_20
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f216,f212,f222])).

fof(f216,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f214,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f215,plain,
    ( spl7_19
    | spl7_3
    | spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f204,f142,f127,f122,f212])).

fof(f142,plain,
    ( spl7_7
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f204,plain,
    ( r1_xboole_0(sK2,sK3)
    | spl7_3
    | spl7_4
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f124,f129,f144,f90])).

fof(f144,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f210,plain,
    ( spl7_18
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f192,f172,f207])).

fof(f192,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f174,f98])).

fof(f203,plain,
    ( spl7_17
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f191,f167,f200])).

fof(f191,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f169,f98])).

fof(f198,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f180,f195])).

fof(f180,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f75,f97])).

fof(f190,plain,
    ( spl7_15
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f179,f172,f187])).

fof(f179,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f174,f97])).

fof(f185,plain,
    ( spl7_14
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f178,f167,f182])).

fof(f178,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f169,f97])).

fof(f175,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f73,f172])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f170,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f70,f167])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f165,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f72,f162])).

fof(f72,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f160,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f69,f157])).

fof(f69,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f155,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f66,f152])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f150,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f64,f147])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f145,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f67,f142])).

fof(f67,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f140,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f71,f137])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f135,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f68,f132])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f130,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f65,f127])).

fof(f65,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f125,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f63,f122])).

fof(f63,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f62,f117])).

fof(f62,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (20301)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (20308)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (20294)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (20309)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (20303)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (20304)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (20300)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (20299)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (20297)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (20298)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (20310)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (20302)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (20295)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (20306)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (20307)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (20314)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (20314)Refutation not found, incomplete strategy% (20314)------------------------------
% 0.20/0.50  % (20314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20314)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (20314)Memory used [KB]: 10618
% 0.20/0.50  % (20314)Time elapsed: 0.096 s
% 0.20/0.50  % (20314)------------------------------
% 0.20/0.50  % (20314)------------------------------
% 0.20/0.50  % (20296)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (20313)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.33/0.52  % (20312)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.33/0.52  % (20305)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.33/0.53  % (20311)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.33/0.53  % (20295)Refutation not found, incomplete strategy% (20295)------------------------------
% 1.33/0.53  % (20295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (20295)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (20295)Memory used [KB]: 10746
% 1.33/0.53  % (20295)Time elapsed: 0.118 s
% 1.33/0.53  % (20295)------------------------------
% 1.33/0.53  % (20295)------------------------------
% 1.47/0.55  % (20294)Refutation not found, incomplete strategy% (20294)------------------------------
% 1.47/0.55  % (20294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (20294)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (20294)Memory used [KB]: 7164
% 1.47/0.55  % (20294)Time elapsed: 0.121 s
% 1.47/0.55  % (20294)------------------------------
% 1.47/0.55  % (20294)------------------------------
% 1.47/0.57  % (20301)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f1162,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f185,f190,f198,f203,f210,f215,f225,f234,f297,f310,f320,f327,f336,f347,f354,f359,f373,f378,f401,f422,f427,f440,f451,f461,f469,f504,f513,f524,f529,f534,f539,f557,f565,f576,f583,f596,f609,f615,f625,f633,f644,f651,f654,f661,f669,f682,f697,f704,f715,f735,f743,f773,f799,f888,f893,f898,f903,f1034,f1039,f1044,f1069,f1086,f1098,f1115,f1129,f1151,f1155,f1159,f1161])).
% 1.47/0.57  fof(f1161,plain,(
% 1.47/0.57    spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_34 | ~spl7_43 | ~spl7_45 | ~spl7_64 | ~spl7_68 | ~spl7_75),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f1160])).
% 1.47/0.57  fof(f1160,plain,(
% 1.47/0.57    $false | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_34 | ~spl7_43 | ~spl7_45 | ~spl7_64 | ~spl7_68 | ~spl7_75)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1149,f1146])).
% 1.47/0.57  fof(f1146,plain,(
% 1.47/0.57    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_34 | ~spl7_43 | ~spl7_45 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1145,f555])).
% 1.47/0.57  fof(f555,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl7_45),
% 1.47/0.57    inference(avatar_component_clause,[],[f554])).
% 1.47/0.57  fof(f554,plain,(
% 1.47/0.57    spl7_45 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.47/0.57  fof(f1145,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_34 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1144,f224])).
% 1.47/0.57  fof(f224,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl7_20),
% 1.47/0.57    inference(avatar_component_clause,[],[f222])).
% 1.47/0.57  fof(f222,plain,(
% 1.47/0.57    spl7_20 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.47/0.57  fof(f1144,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_34 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1143,f300])).
% 1.47/0.57  fof(f300,plain,(
% 1.47/0.57    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) ) | ~spl7_9),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f154,f96])).
% 1.47/0.57  fof(f96,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.47/0.57  fof(f154,plain,(
% 1.47/0.57    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_9),
% 1.47/0.57    inference(avatar_component_clause,[],[f152])).
% 1.47/0.57  fof(f152,plain,(
% 1.47/0.57    spl7_9 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.47/0.57  fof(f1143,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_34 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1130,f403])).
% 1.47/0.57  fof(f403,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) ) | (~spl7_6 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f139,f174,f99])).
% 1.47/0.57  fof(f99,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f44])).
% 1.47/0.57  fof(f44,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.57    inference(flattening,[],[f43])).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f14])).
% 1.47/0.57  fof(f14,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.47/0.57  fof(f174,plain,(
% 1.47/0.57    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_13),
% 1.47/0.57    inference(avatar_component_clause,[],[f172])).
% 1.47/0.57  fof(f172,plain,(
% 1.47/0.57    spl7_13 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.47/0.57  fof(f139,plain,(
% 1.47/0.57    v1_funct_1(sK5) | ~spl7_6),
% 1.47/0.57    inference(avatar_component_clause,[],[f137])).
% 1.47/0.57  fof(f137,plain,(
% 1.47/0.57    spl7_6 <=> v1_funct_1(sK5)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.47/0.57  fof(f1130,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_34 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f114,f119,f124,f134,f129,f139,f149,f154,f159,f164,f169,f174,f533,f892,f431,f1038,f106])).
% 1.47/0.57  fof(f106,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(equality_resolution,[],[f76])).
% 1.47/0.57  fof(f76,plain,(
% 1.47/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f55])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f54])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.57    inference(nnf_transformation,[],[f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f17])).
% 1.47/0.57  fof(f17,axiom,(
% 1.47/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.47/0.57  fof(f1038,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl7_68),
% 1.47/0.57    inference(avatar_component_clause,[],[f1036])).
% 1.47/0.57  fof(f1036,plain,(
% 1.47/0.57    spl7_68 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 1.47/0.57  fof(f431,plain,(
% 1.47/0.57    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl7_34),
% 1.47/0.57    inference(avatar_component_clause,[],[f429])).
% 1.47/0.57  fof(f429,plain,(
% 1.47/0.57    spl7_34 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.47/0.57  fof(f892,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~spl7_64),
% 1.47/0.57    inference(avatar_component_clause,[],[f890])).
% 1.47/0.57  fof(f890,plain,(
% 1.47/0.57    spl7_64 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 1.47/0.57  fof(f533,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl7_43),
% 1.47/0.57    inference(avatar_component_clause,[],[f531])).
% 1.47/0.57  fof(f531,plain,(
% 1.47/0.57    spl7_43 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 1.47/0.57  fof(f169,plain,(
% 1.47/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_12),
% 1.47/0.57    inference(avatar_component_clause,[],[f167])).
% 1.47/0.57  fof(f167,plain,(
% 1.47/0.57    spl7_12 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.47/0.57  fof(f164,plain,(
% 1.47/0.57    v1_funct_2(sK5,sK3,sK1) | ~spl7_11),
% 1.47/0.57    inference(avatar_component_clause,[],[f162])).
% 1.47/0.57  fof(f162,plain,(
% 1.47/0.57    spl7_11 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.47/0.57  fof(f159,plain,(
% 1.47/0.57    v1_funct_2(sK4,sK2,sK1) | ~spl7_10),
% 1.47/0.57    inference(avatar_component_clause,[],[f157])).
% 1.47/0.57  fof(f157,plain,(
% 1.47/0.57    spl7_10 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.47/0.57  fof(f149,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl7_8),
% 1.47/0.57    inference(avatar_component_clause,[],[f147])).
% 1.47/0.57  fof(f147,plain,(
% 1.47/0.57    spl7_8 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.47/0.57  fof(f129,plain,(
% 1.47/0.57    ~v1_xboole_0(sK3) | spl7_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f127])).
% 1.47/0.57  fof(f127,plain,(
% 1.47/0.57    spl7_4 <=> v1_xboole_0(sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.47/0.57  fof(f134,plain,(
% 1.47/0.57    v1_funct_1(sK4) | ~spl7_5),
% 1.47/0.57    inference(avatar_component_clause,[],[f132])).
% 1.47/0.57  fof(f132,plain,(
% 1.47/0.57    spl7_5 <=> v1_funct_1(sK4)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.47/0.57  fof(f124,plain,(
% 1.47/0.57    ~v1_xboole_0(sK2) | spl7_3),
% 1.47/0.57    inference(avatar_component_clause,[],[f122])).
% 1.47/0.57  fof(f122,plain,(
% 1.47/0.57    spl7_3 <=> v1_xboole_0(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.47/0.57  fof(f119,plain,(
% 1.47/0.57    ~v1_xboole_0(sK1) | spl7_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f117])).
% 1.47/0.57  fof(f117,plain,(
% 1.47/0.57    spl7_2 <=> v1_xboole_0(sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.47/0.57  fof(f114,plain,(
% 1.47/0.57    ~v1_xboole_0(sK0) | spl7_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f112])).
% 1.47/0.57  fof(f112,plain,(
% 1.47/0.57    spl7_1 <=> v1_xboole_0(sK0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.47/0.57  fof(f1149,plain,(
% 1.47/0.57    k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | ~spl7_75),
% 1.47/0.57    inference(avatar_component_clause,[],[f1148])).
% 1.47/0.57  fof(f1148,plain,(
% 1.47/0.57    spl7_75 <=> k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 1.47/0.57  fof(f1159,plain,(
% 1.47/0.57    ~spl7_5 | ~spl7_12 | ~spl7_47 | spl7_75),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f1158])).
% 1.47/0.57  fof(f1158,plain,(
% 1.47/0.57    $false | (~spl7_5 | ~spl7_12 | ~spl7_47 | spl7_75)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1157,f134])).
% 1.47/0.57  fof(f1157,plain,(
% 1.47/0.57    ~v1_funct_1(sK4) | (~spl7_12 | ~spl7_47 | spl7_75)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1156,f169])).
% 1.47/0.57  fof(f1156,plain,(
% 1.47/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | (~spl7_47 | spl7_75)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1153,f575])).
% 1.47/0.57  fof(f575,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_47),
% 1.47/0.57    inference(avatar_component_clause,[],[f573])).
% 1.47/0.57  fof(f573,plain,(
% 1.47/0.57    spl7_47 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 1.47/0.57  fof(f1153,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | spl7_75),
% 1.47/0.57    inference(superposition,[],[f1150,f99])).
% 1.47/0.57  fof(f1150,plain,(
% 1.47/0.57    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | spl7_75),
% 1.47/0.57    inference(avatar_component_clause,[],[f1148])).
% 1.47/0.57  fof(f1155,plain,(
% 1.47/0.57    ~spl7_5 | ~spl7_12 | ~spl7_47 | spl7_75),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f1154])).
% 1.47/0.57  fof(f1154,plain,(
% 1.47/0.57    $false | (~spl7_5 | ~spl7_12 | ~spl7_47 | spl7_75)),
% 1.47/0.57    inference(subsumption_resolution,[],[f1152,f575])).
% 1.47/0.57  fof(f1152,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl7_5 | ~spl7_12 | spl7_75)),
% 1.47/0.57    inference(superposition,[],[f1150,f402])).
% 1.47/0.57  fof(f402,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | (~spl7_5 | ~spl7_12)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f134,f169,f99])).
% 1.47/0.57  fof(f1151,plain,(
% 1.47/0.57    ~spl7_75 | spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_35 | ~spl7_43 | ~spl7_45 | ~spl7_64 | ~spl7_68),
% 1.47/0.57    inference(avatar_split_clause,[],[f1142,f1036,f890,f554,f531,f433,f222,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f112,f1148])).
% 1.47/0.57  fof(f433,plain,(
% 1.47/0.57    spl7_35 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.47/0.57  fof(f1142,plain,(
% 1.47/0.57    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_35 | ~spl7_43 | ~spl7_45 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1141,f555])).
% 1.47/0.57  fof(f1141,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_20 | spl7_35 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1140,f224])).
% 1.47/0.57  fof(f1140,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_35 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1139,f300])).
% 1.47/0.57  fof(f1139,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_35 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(forward_demodulation,[],[f1131,f403])).
% 1.47/0.57  fof(f1131,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_35 | ~spl7_43 | ~spl7_64 | ~spl7_68)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f114,f119,f124,f134,f129,f139,f149,f154,f159,f164,f169,f174,f533,f892,f435,f1038,f105])).
% 1.47/0.57  fof(f105,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(equality_resolution,[],[f77])).
% 1.47/0.57  fof(f77,plain,(
% 1.47/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f55])).
% 1.47/0.57  fof(f435,plain,(
% 1.47/0.57    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl7_35),
% 1.47/0.57    inference(avatar_component_clause,[],[f433])).
% 1.47/0.57  fof(f1129,plain,(
% 1.47/0.57    spl7_74 | spl7_2 | ~spl7_42 | ~spl7_63 | ~spl7_67),
% 1.47/0.57    inference(avatar_split_clause,[],[f1087,f1031,f885,f526,f117,f1126])).
% 1.47/0.57  fof(f1126,plain,(
% 1.47/0.57    spl7_74 <=> v1_partfun1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 1.47/0.57  fof(f526,plain,(
% 1.47/0.57    spl7_42 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.47/0.57  fof(f885,plain,(
% 1.47/0.57    spl7_63 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 1.47/0.57  fof(f1031,plain,(
% 1.47/0.57    spl7_67 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 1.47/0.57  fof(f1087,plain,(
% 1.47/0.57    v1_partfun1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2)) | (spl7_2 | ~spl7_42 | ~spl7_63 | ~spl7_67)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f528,f887,f1033,f87])).
% 1.47/0.57  fof(f87,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.47/0.57    inference(flattening,[],[f32])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,axiom,(
% 1.47/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.47/0.57  fof(f1033,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1))) | ~spl7_67),
% 1.47/0.57    inference(avatar_component_clause,[],[f1031])).
% 1.47/0.57  fof(f887,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1) | ~spl7_63),
% 1.47/0.57    inference(avatar_component_clause,[],[f885])).
% 1.47/0.57  fof(f528,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) | ~spl7_42),
% 1.47/0.57    inference(avatar_component_clause,[],[f526])).
% 1.47/0.57  fof(f1115,plain,(
% 1.47/0.57    spl7_73 | ~spl7_66),
% 1.47/0.57    inference(avatar_split_clause,[],[f1047,f900,f1112])).
% 1.47/0.57  fof(f1112,plain,(
% 1.47/0.57    spl7_73 <=> v4_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 1.47/0.57  fof(f900,plain,(
% 1.47/0.57    spl7_66 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 1.47/0.57  fof(f1047,plain,(
% 1.47/0.57    v4_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2)) | ~spl7_66),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f902,f98])).
% 1.47/0.57  fof(f98,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f22])).
% 1.47/0.57  fof(f22,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.47/0.57    inference(pure_predicate_removal,[],[f11])).
% 1.47/0.57  fof(f11,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.47/0.57  fof(f902,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | ~spl7_66),
% 1.47/0.57    inference(avatar_component_clause,[],[f900])).
% 1.47/0.57  fof(f1098,plain,(
% 1.47/0.57    spl7_72 | ~spl7_67),
% 1.47/0.57    inference(avatar_split_clause,[],[f1088,f1031,f1095])).
% 1.47/0.57  fof(f1095,plain,(
% 1.47/0.57    spl7_72 <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 1.47/0.57  fof(f1088,plain,(
% 1.47/0.57    v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) | ~spl7_67),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f1033,f97])).
% 1.47/0.57  fof(f97,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f41])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.57  fof(f1086,plain,(
% 1.47/0.57    spl7_71 | spl7_2 | ~spl7_41 | ~spl7_62 | ~spl7_66),
% 1.47/0.57    inference(avatar_split_clause,[],[f1045,f900,f796,f521,f117,f1083])).
% 1.47/0.57  fof(f1083,plain,(
% 1.47/0.57    spl7_71 <=> v1_partfun1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 1.47/0.57  fof(f521,plain,(
% 1.47/0.57    spl7_41 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 1.47/0.57  fof(f796,plain,(
% 1.47/0.57    spl7_62 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 1.47/0.57  fof(f1045,plain,(
% 1.47/0.57    v1_partfun1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2)) | (spl7_2 | ~spl7_41 | ~spl7_62 | ~spl7_66)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f523,f798,f902,f87])).
% 1.47/0.57  fof(f798,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | ~spl7_62),
% 1.47/0.57    inference(avatar_component_clause,[],[f796])).
% 1.47/0.57  fof(f523,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~spl7_41),
% 1.47/0.57    inference(avatar_component_clause,[],[f521])).
% 1.47/0.57  fof(f1069,plain,(
% 1.47/0.57    spl7_70 | ~spl7_66),
% 1.47/0.57    inference(avatar_split_clause,[],[f1046,f900,f1066])).
% 1.47/0.57  fof(f1066,plain,(
% 1.47/0.57    spl7_70 <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 1.47/0.57  fof(f1046,plain,(
% 1.47/0.57    v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~spl7_66),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f902,f97])).
% 1.47/0.57  fof(f1044,plain,(
% 1.47/0.57    spl7_69 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f547,f172,f162,f152,f137,f127,f117,f1041])).
% 1.47/0.57  fof(f1041,plain,(
% 1.47/0.57    spl7_69 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 1.47/0.57  fof(f547,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | (spl7_2 | spl7_4 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f129,f139,f129,f139,f154,f154,f164,f174,f164,f174,f108])).
% 1.47/0.57  fof(f108,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f102,f80])).
% 1.47/0.57  fof(f80,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.47/0.57  fof(f102,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f45])).
% 1.47/0.57  fof(f45,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f18])).
% 1.47/0.57  fof(f18,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.47/0.57  fof(f1039,plain,(
% 1.47/0.57    spl7_68 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f546,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f1036])).
% 1.47/0.57  fof(f546,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f124,f134,f129,f139,f149,f154,f159,f169,f164,f174,f108])).
% 1.47/0.57  fof(f1034,plain,(
% 1.47/0.57    spl7_67 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f545,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f1031])).
% 1.47/0.57  fof(f545,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1))) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f129,f139,f124,f134,f154,f149,f164,f174,f159,f169,f108])).
% 1.47/0.57  fof(f903,plain,(
% 1.47/0.57    spl7_66 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_10 | ~spl7_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f544,f167,f157,f147,f132,f122,f117,f900])).
% 1.47/0.57  fof(f544,plain,(
% 1.47/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_10 | ~spl7_12)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f124,f134,f124,f134,f149,f149,f159,f169,f159,f169,f108])).
% 1.47/0.57  fof(f898,plain,(
% 1.47/0.57    spl7_65 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f543,f172,f162,f152,f137,f127,f117,f895])).
% 1.47/0.57  fof(f895,plain,(
% 1.47/0.57    spl7_65 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 1.47/0.57  fof(f543,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | (spl7_2 | spl7_4 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f129,f139,f129,f139,f154,f154,f164,f174,f164,f174,f109])).
% 1.47/0.57  fof(f109,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f101,f80])).
% 1.47/0.57  fof(f101,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f893,plain,(
% 1.47/0.57    spl7_64 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f542,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f890])).
% 1.47/0.57  fof(f542,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f124,f134,f129,f139,f149,f154,f159,f169,f164,f174,f109])).
% 1.47/0.57  fof(f888,plain,(
% 1.47/0.57    spl7_63 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f541,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f885])).
% 1.47/0.57  fof(f541,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f129,f139,f124,f134,f154,f149,f164,f174,f159,f169,f109])).
% 1.47/0.57  fof(f799,plain,(
% 1.47/0.57    spl7_62 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_10 | ~spl7_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f540,f167,f157,f147,f132,f122,f117,f796])).
% 1.47/0.57  fof(f540,plain,(
% 1.47/0.57    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_10 | ~spl7_12)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f124,f134,f124,f134,f149,f149,f159,f169,f159,f169,f109])).
% 1.47/0.57  fof(f773,plain,(
% 1.47/0.57    spl7_61 | ~spl7_22 | ~spl7_37),
% 1.47/0.57    inference(avatar_split_clause,[],[f692,f458,f294,f770])).
% 1.47/0.57  fof(f770,plain,(
% 1.47/0.57    spl7_61 <=> k1_xboole_0 = k7_relat_1(sK6(sK3),k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 1.47/0.57  fof(f294,plain,(
% 1.47/0.57    spl7_22 <=> k1_xboole_0 = k7_relat_1(sK6(sK3),sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.47/0.57  fof(f458,plain,(
% 1.47/0.57    spl7_37 <=> k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.47/0.57  fof(f692,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK6(sK3),k1_xboole_0) | (~spl7_22 | ~spl7_37)),
% 1.47/0.57    inference(forward_demodulation,[],[f687,f296])).
% 1.47/0.57  fof(f296,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK6(sK3),sK2) | ~spl7_22),
% 1.47/0.57    inference(avatar_component_clause,[],[f294])).
% 1.47/0.57  fof(f687,plain,(
% 1.47/0.57    k7_relat_1(sK6(sK3),sK2) = k7_relat_1(sK6(sK3),k1_xboole_0) | ~spl7_37),
% 1.47/0.57    inference(superposition,[],[f277,f460])).
% 1.47/0.57  fof(f460,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK3,sK2) | ~spl7_37),
% 1.47/0.57    inference(avatar_component_clause,[],[f458])).
% 1.47/0.57  fof(f277,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k7_relat_1(sK6(X0),X1) = k7_relat_1(sK6(X0),k3_xboole_0(X0,X1))) )),
% 1.47/0.57    inference(backward_demodulation,[],[f252,f276])).
% 1.47/0.57  fof(f276,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(sK6(X0),X1))) )),
% 1.47/0.57    inference(backward_demodulation,[],[f238,f270])).
% 1.47/0.57  fof(f270,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f82,f83,f85,f92])).
% 1.47/0.57  fof(f92,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f59])).
% 1.47/0.57  fof(f59,plain,(
% 1.47/0.57    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(nnf_transformation,[],[f39])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(flattening,[],[f38])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.47/0.57    inference(ennf_transformation,[],[f13])).
% 1.47/0.57  fof(f13,axiom,(
% 1.47/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.47/0.57  fof(f85,plain,(
% 1.47/0.57    ( ! [X0] : (v1_partfun1(sK6(X0),X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f57])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    ! [X0] : (v1_partfun1(sK6(X0),X0) & v1_funct_1(sK6(X0)) & v4_relat_1(sK6(X0),X0) & v1_relat_1(sK6(X0)))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f56])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    ! [X0] : (? [X1] : (v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(sK6(X0),X0) & v1_funct_1(sK6(X0)) & v4_relat_1(sK6(X0),X0) & v1_relat_1(sK6(X0))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ! [X0] : ? [X1] : (v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 1.47/0.57    inference(pure_predicate_removal,[],[f15])).
% 1.47/0.57  fof(f15,axiom,(
% 1.47/0.57    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).
% 1.47/0.57  fof(f83,plain,(
% 1.47/0.57    ( ! [X0] : (v4_relat_1(sK6(X0),X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f57])).
% 1.47/0.57  fof(f82,plain,(
% 1.47/0.57    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f57])).
% 1.47/0.57  fof(f238,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(sK6(X0)),X1) = k1_relat_1(k7_relat_1(sK6(X0),X1))) )),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f82,f88])).
% 1.47/0.57  fof(f88,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(ennf_transformation,[],[f8])).
% 1.47/0.57  fof(f8,axiom,(
% 1.47/0.57    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.47/0.57  fof(f252,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k7_relat_1(sK6(X0),X1) = k7_relat_1(sK6(X0),k1_relat_1(k7_relat_1(sK6(X0),X1)))) )),
% 1.47/0.57    inference(forward_demodulation,[],[f246,f238])).
% 1.47/0.57  fof(f246,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k7_relat_1(sK6(X0),X1) = k7_relat_1(sK6(X0),k3_xboole_0(k1_relat_1(sK6(X0)),X1))) )),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f82,f89])).
% 1.47/0.57  fof(f89,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(ennf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 1.47/0.57  fof(f743,plain,(
% 1.47/0.57    spl7_60 | ~spl7_59),
% 1.47/0.57    inference(avatar_split_clause,[],[f736,f732,f740])).
% 1.47/0.57  fof(f740,plain,(
% 1.47/0.57    spl7_60 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 1.47/0.57  fof(f732,plain,(
% 1.47/0.57    spl7_59 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 1.47/0.57  fof(f736,plain,(
% 1.47/0.57    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_59),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f734,f95])).
% 1.47/0.57  fof(f95,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f60])).
% 1.47/0.57  fof(f60,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.47/0.57    inference(nnf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.57  fof(f734,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_59),
% 1.47/0.57    inference(avatar_component_clause,[],[f732])).
% 1.47/0.57  fof(f735,plain,(
% 1.47/0.57    spl7_59 | ~spl7_25 | ~spl7_27 | ~spl7_58),
% 1.47/0.57    inference(avatar_split_clause,[],[f730,f712,f333,f317,f732])).
% 1.47/0.57  fof(f317,plain,(
% 1.47/0.57    spl7_25 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.47/0.57  fof(f333,plain,(
% 1.47/0.57    spl7_27 <=> k1_xboole_0 = sK6(k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.47/0.57  fof(f712,plain,(
% 1.47/0.57    spl7_58 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 1.47/0.57  fof(f730,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl7_25 | ~spl7_27 | ~spl7_58)),
% 1.47/0.57    inference(forward_demodulation,[],[f729,f318])).
% 1.47/0.57  fof(f318,plain,(
% 1.47/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_25),
% 1.47/0.57    inference(avatar_component_clause,[],[f317])).
% 1.47/0.57  fof(f729,plain,(
% 1.47/0.57    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl7_27 | ~spl7_58)),
% 1.47/0.57    inference(superposition,[],[f337,f714])).
% 1.47/0.57  fof(f714,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl7_58),
% 1.47/0.57    inference(avatar_component_clause,[],[f712])).
% 1.47/0.57  fof(f337,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl7_27),
% 1.47/0.57    inference(superposition,[],[f276,f335])).
% 1.47/0.57  fof(f335,plain,(
% 1.47/0.57    k1_xboole_0 = sK6(k1_xboole_0) | ~spl7_27),
% 1.47/0.57    inference(avatar_component_clause,[],[f333])).
% 1.47/0.57  fof(f715,plain,(
% 1.47/0.57    spl7_58 | ~spl7_27 | ~spl7_51 | ~spl7_52),
% 1.47/0.57    inference(avatar_split_clause,[],[f690,f622,f612,f333,f712])).
% 1.47/0.57  fof(f612,plain,(
% 1.47/0.57    spl7_51 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 1.47/0.57  fof(f622,plain,(
% 1.47/0.57    spl7_52 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 1.47/0.57  fof(f690,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_27 | ~spl7_51 | ~spl7_52)),
% 1.47/0.57    inference(forward_demodulation,[],[f689,f614])).
% 1.47/0.57  fof(f614,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) | ~spl7_51),
% 1.47/0.57    inference(avatar_component_clause,[],[f612])).
% 1.47/0.57  fof(f689,plain,(
% 1.47/0.57    k7_relat_1(k1_xboole_0,sK2) = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_27 | ~spl7_52)),
% 1.47/0.57    inference(forward_demodulation,[],[f684,f335])).
% 1.47/0.57  fof(f684,plain,(
% 1.47/0.57    k7_relat_1(sK6(k1_xboole_0),sK2) = k7_relat_1(sK6(k1_xboole_0),k1_xboole_0) | ~spl7_52),
% 1.47/0.57    inference(superposition,[],[f277,f624])).
% 1.47/0.57  fof(f624,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl7_52),
% 1.47/0.57    inference(avatar_component_clause,[],[f622])).
% 1.47/0.57  fof(f704,plain,(
% 1.47/0.57    spl7_50 | ~spl7_25 | ~spl7_27 | ~spl7_57),
% 1.47/0.57    inference(avatar_split_clause,[],[f695,f679,f333,f317,f606])).
% 1.47/0.57  fof(f606,plain,(
% 1.47/0.57    spl7_50 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 1.47/0.57  fof(f679,plain,(
% 1.47/0.57    spl7_57 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 1.47/0.57  fof(f695,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK3) | (~spl7_25 | ~spl7_27 | ~spl7_57)),
% 1.47/0.57    inference(forward_demodulation,[],[f694,f318])).
% 1.47/0.57  fof(f694,plain,(
% 1.47/0.57    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK3) | (~spl7_27 | ~spl7_57)),
% 1.47/0.57    inference(superposition,[],[f337,f681])).
% 1.47/0.57  fof(f681,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) | ~spl7_57),
% 1.47/0.57    inference(avatar_component_clause,[],[f679])).
% 1.47/0.57  fof(f697,plain,(
% 1.47/0.57    ~spl7_25 | ~spl7_27 | spl7_50 | ~spl7_57),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f696])).
% 1.47/0.57  fof(f696,plain,(
% 1.47/0.57    $false | (~spl7_25 | ~spl7_27 | spl7_50 | ~spl7_57)),
% 1.47/0.57    inference(subsumption_resolution,[],[f695,f608])).
% 1.47/0.57  fof(f608,plain,(
% 1.47/0.57    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK3) | spl7_50),
% 1.47/0.57    inference(avatar_component_clause,[],[f606])).
% 1.47/0.57  fof(f682,plain,(
% 1.47/0.57    spl7_57 | ~spl7_27 | ~spl7_56),
% 1.47/0.57    inference(avatar_split_clause,[],[f676,f666,f333,f679])).
% 1.47/0.57  fof(f666,plain,(
% 1.47/0.57    spl7_56 <=> r1_xboole_0(sK3,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 1.47/0.57  fof(f676,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) | (~spl7_27 | ~spl7_56)),
% 1.47/0.57    inference(forward_demodulation,[],[f671,f335])).
% 1.47/0.57  fof(f671,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK6(k1_xboole_0),sK3) | ~spl7_56),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f668,f282])).
% 1.47/0.57  fof(f282,plain,(
% 1.47/0.57    ( ! [X4,X5] : (~r1_xboole_0(X5,X4) | k1_xboole_0 = k7_relat_1(sK6(X4),X5)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f280,f82])).
% 1.47/0.57  fof(f280,plain,(
% 1.47/0.57    ( ! [X4,X5] : (~r1_xboole_0(X5,X4) | k1_xboole_0 = k7_relat_1(sK6(X4),X5) | ~v1_relat_1(sK6(X4))) )),
% 1.47/0.57    inference(superposition,[],[f79,f270])).
% 1.47/0.57  fof(f79,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.47/0.57  fof(f668,plain,(
% 1.47/0.57    r1_xboole_0(sK3,k1_xboole_0) | ~spl7_56),
% 1.47/0.57    inference(avatar_component_clause,[],[f666])).
% 1.47/0.57  fof(f669,plain,(
% 1.47/0.57    spl7_56 | ~spl7_55),
% 1.47/0.57    inference(avatar_split_clause,[],[f662,f658,f666])).
% 1.47/0.57  fof(f658,plain,(
% 1.47/0.57    spl7_55 <=> k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 1.47/0.57  fof(f662,plain,(
% 1.47/0.57    r1_xboole_0(sK3,k1_xboole_0) | ~spl7_55),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f660,f95])).
% 1.47/0.57  fof(f660,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0) | ~spl7_55),
% 1.47/0.57    inference(avatar_component_clause,[],[f658])).
% 1.47/0.57  fof(f661,plain,(
% 1.47/0.57    spl7_55 | ~spl7_15 | ~spl7_18 | ~spl7_25 | ~spl7_30 | ~spl7_45),
% 1.47/0.57    inference(avatar_split_clause,[],[f656,f554,f375,f317,f207,f187,f658])).
% 1.47/0.57  fof(f187,plain,(
% 1.47/0.57    spl7_15 <=> v1_relat_1(sK5)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.47/0.57  fof(f207,plain,(
% 1.47/0.57    spl7_18 <=> v4_relat_1(sK5,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.47/0.57  fof(f375,plain,(
% 1.47/0.57    spl7_30 <=> v1_partfun1(sK5,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.47/0.57  fof(f656,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK3,k1_xboole_0) | (~spl7_15 | ~spl7_18 | ~spl7_25 | ~spl7_30 | ~spl7_45)),
% 1.47/0.57    inference(forward_demodulation,[],[f655,f318])).
% 1.47/0.57  fof(f655,plain,(
% 1.47/0.57    k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,k1_xboole_0) | (~spl7_15 | ~spl7_18 | ~spl7_30 | ~spl7_45)),
% 1.47/0.57    inference(superposition,[],[f392,f555])).
% 1.47/0.57  fof(f392,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0)) ) | (~spl7_15 | ~spl7_18 | ~spl7_30)),
% 1.47/0.57    inference(backward_demodulation,[],[f237,f388])).
% 1.47/0.57  fof(f388,plain,(
% 1.47/0.57    sK3 = k1_relat_1(sK5) | (~spl7_15 | ~spl7_18 | ~spl7_30)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f189,f209,f377,f92])).
% 1.47/0.57  fof(f377,plain,(
% 1.47/0.57    v1_partfun1(sK5,sK3) | ~spl7_30),
% 1.47/0.57    inference(avatar_component_clause,[],[f375])).
% 1.47/0.57  fof(f209,plain,(
% 1.47/0.57    v4_relat_1(sK5,sK3) | ~spl7_18),
% 1.47/0.57    inference(avatar_component_clause,[],[f207])).
% 1.47/0.57  fof(f189,plain,(
% 1.47/0.57    v1_relat_1(sK5) | ~spl7_15),
% 1.47/0.57    inference(avatar_component_clause,[],[f187])).
% 1.47/0.57  fof(f237,plain,(
% 1.47/0.57    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK5),X0) = k1_relat_1(k7_relat_1(sK5,X0))) ) | ~spl7_15),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f189,f88])).
% 1.47/0.57  fof(f654,plain,(
% 1.47/0.57    spl7_45 | ~spl7_15 | ~spl7_18 | ~spl7_30 | ~spl7_37 | ~spl7_40),
% 1.47/0.57    inference(avatar_split_clause,[],[f649,f510,f458,f375,f207,f187,f554])).
% 1.47/0.57  fof(f510,plain,(
% 1.47/0.57    spl7_40 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.47/0.57  fof(f649,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl7_15 | ~spl7_18 | ~spl7_30 | ~spl7_37 | ~spl7_40)),
% 1.47/0.57    inference(forward_demodulation,[],[f647,f512])).
% 1.47/0.57  fof(f512,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl7_40),
% 1.47/0.57    inference(avatar_component_clause,[],[f510])).
% 1.47/0.57  fof(f647,plain,(
% 1.47/0.57    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) | (~spl7_15 | ~spl7_18 | ~spl7_30 | ~spl7_37)),
% 1.47/0.57    inference(superposition,[],[f395,f460])).
% 1.47/0.57  fof(f395,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0))) ) | (~spl7_15 | ~spl7_18 | ~spl7_30)),
% 1.47/0.57    inference(backward_demodulation,[],[f253,f392])).
% 1.47/0.57  fof(f253,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0)))) ) | ~spl7_15),
% 1.47/0.57    inference(forward_demodulation,[],[f245,f237])).
% 1.47/0.57  fof(f245,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0))) ) | ~spl7_15),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f189,f89])).
% 1.47/0.57  fof(f651,plain,(
% 1.47/0.57    ~spl7_15 | ~spl7_18 | ~spl7_30 | ~spl7_37 | ~spl7_40 | spl7_45),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f650])).
% 1.47/0.57  fof(f650,plain,(
% 1.47/0.57    $false | (~spl7_15 | ~spl7_18 | ~spl7_30 | ~spl7_37 | ~spl7_40 | spl7_45)),
% 1.47/0.57    inference(subsumption_resolution,[],[f649,f556])).
% 1.47/0.57  fof(f556,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | spl7_45),
% 1.47/0.57    inference(avatar_component_clause,[],[f554])).
% 1.47/0.57  fof(f644,plain,(
% 1.47/0.57    spl7_54 | ~spl7_53),
% 1.47/0.57    inference(avatar_split_clause,[],[f635,f630,f641])).
% 1.47/0.57  fof(f641,plain,(
% 1.47/0.57    spl7_54 <=> k1_xboole_0 = k7_relat_1(sK6(sK2),k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 1.47/0.57  fof(f630,plain,(
% 1.47/0.57    spl7_53 <=> r1_xboole_0(k1_xboole_0,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 1.47/0.57  fof(f635,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK6(sK2),k1_xboole_0) | ~spl7_53),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f632,f282])).
% 1.47/0.57  fof(f632,plain,(
% 1.47/0.57    r1_xboole_0(k1_xboole_0,sK2) | ~spl7_53),
% 1.47/0.57    inference(avatar_component_clause,[],[f630])).
% 1.47/0.57  fof(f633,plain,(
% 1.47/0.57    spl7_53 | ~spl7_52),
% 1.47/0.57    inference(avatar_split_clause,[],[f626,f622,f630])).
% 1.47/0.57  fof(f626,plain,(
% 1.47/0.57    r1_xboole_0(k1_xboole_0,sK2) | ~spl7_52),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f624,f95])).
% 1.47/0.57  fof(f625,plain,(
% 1.47/0.57    spl7_52 | ~spl7_25 | ~spl7_27 | ~spl7_51),
% 1.47/0.57    inference(avatar_split_clause,[],[f620,f612,f333,f317,f622])).
% 1.47/0.57  fof(f620,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | (~spl7_25 | ~spl7_27 | ~spl7_51)),
% 1.47/0.57    inference(forward_demodulation,[],[f619,f318])).
% 1.47/0.57  fof(f619,plain,(
% 1.47/0.57    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK2) | (~spl7_27 | ~spl7_51)),
% 1.47/0.57    inference(superposition,[],[f337,f614])).
% 1.47/0.57  fof(f615,plain,(
% 1.47/0.57    spl7_51 | ~spl7_27 | ~spl7_49),
% 1.47/0.57    inference(avatar_split_clause,[],[f603,f593,f333,f612])).
% 1.47/0.57  fof(f593,plain,(
% 1.47/0.57    spl7_49 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 1.47/0.57  fof(f603,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) | (~spl7_27 | ~spl7_49)),
% 1.47/0.57    inference(forward_demodulation,[],[f598,f335])).
% 1.47/0.57  fof(f598,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK6(k1_xboole_0),sK2) | ~spl7_49),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f595,f282])).
% 1.47/0.57  fof(f595,plain,(
% 1.47/0.57    r1_xboole_0(sK2,k1_xboole_0) | ~spl7_49),
% 1.47/0.57    inference(avatar_component_clause,[],[f593])).
% 1.47/0.57  fof(f609,plain,(
% 1.47/0.57    ~spl7_50 | spl7_46),
% 1.47/0.57    inference(avatar_split_clause,[],[f571,f562,f606])).
% 1.47/0.57  fof(f562,plain,(
% 1.47/0.57    spl7_46 <=> r1_xboole_0(k1_xboole_0,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.47/0.57  fof(f571,plain,(
% 1.47/0.57    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK3) | spl7_46),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f564,f95])).
% 1.47/0.57  fof(f564,plain,(
% 1.47/0.57    ~r1_xboole_0(k1_xboole_0,sK3) | spl7_46),
% 1.47/0.57    inference(avatar_component_clause,[],[f562])).
% 1.47/0.57  fof(f596,plain,(
% 1.47/0.57    spl7_49 | ~spl7_48),
% 1.47/0.57    inference(avatar_split_clause,[],[f584,f580,f593])).
% 1.47/0.57  fof(f580,plain,(
% 1.47/0.57    spl7_48 <=> k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 1.47/0.57  fof(f584,plain,(
% 1.47/0.57    r1_xboole_0(sK2,k1_xboole_0) | ~spl7_48),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f582,f95])).
% 1.47/0.57  fof(f582,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0) | ~spl7_48),
% 1.47/0.57    inference(avatar_component_clause,[],[f580])).
% 1.47/0.57  fof(f583,plain,(
% 1.47/0.57    spl7_48 | ~spl7_14 | ~spl7_17 | ~spl7_25 | ~spl7_29 | ~spl7_47),
% 1.47/0.57    inference(avatar_split_clause,[],[f578,f573,f370,f317,f200,f182,f580])).
% 1.47/0.57  fof(f182,plain,(
% 1.47/0.57    spl7_14 <=> v1_relat_1(sK4)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.47/0.57  fof(f200,plain,(
% 1.47/0.57    spl7_17 <=> v4_relat_1(sK4,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.47/0.57  fof(f370,plain,(
% 1.47/0.57    spl7_29 <=> v1_partfun1(sK4,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 1.47/0.57  fof(f578,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0) | (~spl7_14 | ~spl7_17 | ~spl7_25 | ~spl7_29 | ~spl7_47)),
% 1.47/0.57    inference(forward_demodulation,[],[f577,f318])).
% 1.47/0.57  fof(f577,plain,(
% 1.47/0.57    k1_relat_1(k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) | (~spl7_14 | ~spl7_17 | ~spl7_29 | ~spl7_47)),
% 1.47/0.57    inference(superposition,[],[f383,f575])).
% 1.47/0.57  fof(f383,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(sK2,X0)) ) | (~spl7_14 | ~spl7_17 | ~spl7_29)),
% 1.47/0.57    inference(backward_demodulation,[],[f236,f379])).
% 1.47/0.57  fof(f379,plain,(
% 1.47/0.57    sK2 = k1_relat_1(sK4) | (~spl7_14 | ~spl7_17 | ~spl7_29)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f184,f202,f372,f92])).
% 1.47/0.57  fof(f372,plain,(
% 1.47/0.57    v1_partfun1(sK4,sK2) | ~spl7_29),
% 1.47/0.57    inference(avatar_component_clause,[],[f370])).
% 1.47/0.57  fof(f202,plain,(
% 1.47/0.57    v4_relat_1(sK4,sK2) | ~spl7_17),
% 1.47/0.57    inference(avatar_component_clause,[],[f200])).
% 1.47/0.57  fof(f184,plain,(
% 1.47/0.57    v1_relat_1(sK4) | ~spl7_14),
% 1.47/0.57    inference(avatar_component_clause,[],[f182])).
% 1.47/0.57  fof(f236,plain,(
% 1.47/0.57    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK4),X0) = k1_relat_1(k7_relat_1(sK4,X0))) ) | ~spl7_14),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f184,f88])).
% 1.47/0.57  fof(f576,plain,(
% 1.47/0.57    spl7_47 | ~spl7_14 | ~spl7_17 | ~spl7_20 | ~spl7_29 | ~spl7_39),
% 1.47/0.57    inference(avatar_split_clause,[],[f550,f501,f370,f222,f200,f182,f573])).
% 1.47/0.57  fof(f501,plain,(
% 1.47/0.57    spl7_39 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.47/0.57  fof(f550,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_14 | ~spl7_17 | ~spl7_20 | ~spl7_29 | ~spl7_39)),
% 1.47/0.57    inference(forward_demodulation,[],[f548,f503])).
% 1.47/0.57  fof(f503,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl7_39),
% 1.47/0.57    inference(avatar_component_clause,[],[f501])).
% 1.47/0.57  fof(f548,plain,(
% 1.47/0.57    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK4,sK3) | (~spl7_14 | ~spl7_17 | ~spl7_20 | ~spl7_29)),
% 1.47/0.57    inference(superposition,[],[f386,f224])).
% 1.47/0.57  fof(f386,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))) ) | (~spl7_14 | ~spl7_17 | ~spl7_29)),
% 1.47/0.57    inference(backward_demodulation,[],[f254,f383])).
% 1.47/0.57  fof(f254,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0)))) ) | ~spl7_14),
% 1.47/0.57    inference(forward_demodulation,[],[f244,f236])).
% 1.47/0.57  fof(f244,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0))) ) | ~spl7_14),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f184,f89])).
% 1.47/0.57  fof(f565,plain,(
% 1.47/0.57    ~spl7_46 | ~spl7_15 | ~spl7_33 | spl7_45),
% 1.47/0.57    inference(avatar_split_clause,[],[f559,f554,f424,f187,f562])).
% 1.47/0.57  fof(f424,plain,(
% 1.47/0.57    spl7_33 <=> sK3 = k1_relat_1(sK5)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.47/0.57  fof(f559,plain,(
% 1.47/0.57    ~r1_xboole_0(k1_xboole_0,sK3) | (~spl7_15 | ~spl7_33 | spl7_45)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f556,f450])).
% 1.47/0.57  fof(f450,plain,(
% 1.47/0.57    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | (~spl7_15 | ~spl7_33)),
% 1.47/0.57    inference(subsumption_resolution,[],[f448,f189])).
% 1.47/0.57  fof(f448,plain,(
% 1.47/0.57    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2) | ~v1_relat_1(sK5)) ) | ~spl7_33),
% 1.47/0.57    inference(superposition,[],[f79,f426])).
% 1.47/0.57  fof(f426,plain,(
% 1.47/0.57    sK3 = k1_relat_1(sK5) | ~spl7_33),
% 1.47/0.57    inference(avatar_component_clause,[],[f424])).
% 1.47/0.57  fof(f557,plain,(
% 1.47/0.57    ~spl7_45 | ~spl7_14 | ~spl7_17 | ~spl7_20 | ~spl7_29 | spl7_36 | ~spl7_39),
% 1.47/0.57    inference(avatar_split_clause,[],[f551,f501,f437,f370,f222,f200,f182,f554])).
% 1.47/0.57  fof(f437,plain,(
% 1.47/0.57    spl7_36 <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 1.47/0.57  fof(f551,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl7_14 | ~spl7_17 | ~spl7_20 | ~spl7_29 | spl7_36 | ~spl7_39)),
% 1.47/0.57    inference(backward_demodulation,[],[f439,f550])).
% 1.47/0.57  fof(f439,plain,(
% 1.47/0.57    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl7_36),
% 1.47/0.57    inference(avatar_component_clause,[],[f437])).
% 1.47/0.57  fof(f539,plain,(
% 1.47/0.57    spl7_44 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f519,f172,f162,f152,f137,f127,f117,f536])).
% 1.47/0.57  fof(f536,plain,(
% 1.47/0.57    spl7_44 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 1.47/0.57  fof(f519,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | (spl7_2 | spl7_4 | ~spl7_6 | ~spl7_9 | ~spl7_11 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f129,f139,f129,f139,f154,f154,f164,f174,f164,f174,f110])).
% 1.47/0.57  fof(f110,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f100,f80])).
% 1.47/0.57  fof(f100,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f534,plain,(
% 1.47/0.57    spl7_43 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f518,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f531])).
% 1.47/0.57  fof(f518,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f124,f134,f129,f139,f149,f154,f159,f169,f164,f174,f110])).
% 1.47/0.57  fof(f529,plain,(
% 1.47/0.57    spl7_42 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f517,f172,f167,f162,f157,f152,f147,f137,f132,f127,f122,f117,f526])).
% 1.47/0.57  fof(f517,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f129,f139,f124,f134,f154,f149,f164,f174,f159,f169,f110])).
% 1.47/0.57  fof(f524,plain,(
% 1.47/0.57    spl7_41 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_10 | ~spl7_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f516,f167,f157,f147,f132,f122,f117,f521])).
% 1.47/0.57  fof(f516,plain,(
% 1.47/0.57    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_8 | ~spl7_10 | ~spl7_12)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f124,f134,f124,f134,f149,f149,f159,f169,f159,f169,f110])).
% 1.47/0.57  fof(f513,plain,(
% 1.47/0.57    spl7_40 | ~spl7_15 | ~spl7_19 | ~spl7_33),
% 1.47/0.57    inference(avatar_split_clause,[],[f507,f424,f212,f187,f510])).
% 1.47/0.57  fof(f212,plain,(
% 1.47/0.57    spl7_19 <=> r1_xboole_0(sK2,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.47/0.57  fof(f507,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl7_15 | ~spl7_19 | ~spl7_33)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f214,f450])).
% 1.47/0.57  fof(f214,plain,(
% 1.47/0.57    r1_xboole_0(sK2,sK3) | ~spl7_19),
% 1.47/0.57    inference(avatar_component_clause,[],[f212])).
% 1.47/0.57  fof(f504,plain,(
% 1.47/0.57    spl7_39 | ~spl7_14 | ~spl7_24 | ~spl7_32),
% 1.47/0.57    inference(avatar_split_clause,[],[f497,f419,f313,f182,f501])).
% 1.47/0.57  fof(f313,plain,(
% 1.47/0.57    spl7_24 <=> r1_xboole_0(sK3,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.47/0.57  fof(f419,plain,(
% 1.47/0.57    spl7_32 <=> sK2 = k1_relat_1(sK4)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.47/0.57  fof(f497,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl7_14 | ~spl7_24 | ~spl7_32)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f315,f445])).
% 1.47/0.57  fof(f445,plain,(
% 1.47/0.57    ( ! [X2] : (~r1_xboole_0(X2,sK2) | k1_xboole_0 = k7_relat_1(sK4,X2)) ) | (~spl7_14 | ~spl7_32)),
% 1.47/0.57    inference(subsumption_resolution,[],[f443,f184])).
% 1.47/0.57  fof(f443,plain,(
% 1.47/0.57    ( ! [X2] : (~r1_xboole_0(X2,sK2) | k1_xboole_0 = k7_relat_1(sK4,X2) | ~v1_relat_1(sK4)) ) | ~spl7_32),
% 1.47/0.57    inference(superposition,[],[f79,f421])).
% 1.47/0.57  fof(f421,plain,(
% 1.47/0.57    sK2 = k1_relat_1(sK4) | ~spl7_32),
% 1.47/0.57    inference(avatar_component_clause,[],[f419])).
% 1.47/0.57  fof(f315,plain,(
% 1.47/0.57    r1_xboole_0(sK3,sK2) | ~spl7_24),
% 1.47/0.57    inference(avatar_component_clause,[],[f313])).
% 1.47/0.57  fof(f469,plain,(
% 1.47/0.57    spl7_38 | ~spl7_24),
% 1.47/0.57    inference(avatar_split_clause,[],[f411,f313,f466])).
% 1.47/0.57  fof(f466,plain,(
% 1.47/0.57    spl7_38 <=> k1_xboole_0 = k7_relat_1(sK6(sK2),sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.47/0.57  fof(f411,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK6(sK2),sK3) | ~spl7_24),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f315,f282])).
% 1.47/0.57  fof(f461,plain,(
% 1.47/0.57    spl7_37 | ~spl7_23 | ~spl7_27),
% 1.47/0.57    inference(avatar_split_clause,[],[f351,f333,f307,f458])).
% 1.47/0.57  fof(f307,plain,(
% 1.47/0.57    spl7_23 <=> k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.47/0.57  fof(f351,plain,(
% 1.47/0.57    k1_xboole_0 = k3_xboole_0(sK3,sK2) | (~spl7_23 | ~spl7_27)),
% 1.47/0.57    inference(backward_demodulation,[],[f309,f338])).
% 1.47/0.57  fof(f338,plain,(
% 1.47/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_27),
% 1.47/0.57    inference(superposition,[],[f270,f335])).
% 1.47/0.57  fof(f309,plain,(
% 1.47/0.57    k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,sK2) | ~spl7_23),
% 1.47/0.57    inference(avatar_component_clause,[],[f307])).
% 1.47/0.57  fof(f451,plain,(
% 1.47/0.57    spl7_25 | ~spl7_27),
% 1.47/0.57    inference(avatar_split_clause,[],[f338,f333,f317])).
% 1.47/0.57  fof(f440,plain,(
% 1.47/0.57    ~spl7_34 | ~spl7_35 | ~spl7_36 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_20),
% 1.47/0.57    inference(avatar_split_clause,[],[f406,f222,f172,f167,f152,f137,f132,f437,f433,f429])).
% 1.47/0.57  fof(f406,plain,(
% 1.47/0.57    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_20)),
% 1.47/0.57    inference(backward_demodulation,[],[f405,f402])).
% 1.47/0.57  fof(f405,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_9 | ~spl7_13 | ~spl7_20)),
% 1.47/0.57    inference(backward_demodulation,[],[f305,f403])).
% 1.47/0.57  fof(f305,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_9 | ~spl7_20)),
% 1.47/0.57    inference(forward_demodulation,[],[f304,f224])).
% 1.47/0.57  fof(f304,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl7_9),
% 1.47/0.57    inference(backward_demodulation,[],[f74,f300])).
% 1.47/0.57  fof(f74,plain,(
% 1.47/0.57    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.47/0.57    inference(cnf_transformation,[],[f53])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f52,f51,f50,f49,f48,f47])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f49,plain,(
% 1.47/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f50,plain,(
% 1.47/0.57    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,negated_conjecture,(
% 1.47/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.47/0.57    inference(negated_conjecture,[],[f19])).
% 1.47/0.57  fof(f19,conjecture,(
% 1.47/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.47/0.57  fof(f427,plain,(
% 1.47/0.57    spl7_33 | ~spl7_15 | ~spl7_18 | ~spl7_30),
% 1.47/0.57    inference(avatar_split_clause,[],[f388,f375,f207,f187,f424])).
% 1.47/0.57  fof(f422,plain,(
% 1.47/0.57    spl7_32 | ~spl7_14 | ~spl7_17 | ~spl7_29),
% 1.47/0.57    inference(avatar_split_clause,[],[f379,f370,f200,f182,f419])).
% 1.47/0.57  fof(f401,plain,(
% 1.47/0.57    spl7_31 | ~spl7_27),
% 1.47/0.57    inference(avatar_split_clause,[],[f339,f333,f398])).
% 1.47/0.57  fof(f398,plain,(
% 1.47/0.57    spl7_31 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.47/0.57  fof(f339,plain,(
% 1.47/0.57    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl7_27),
% 1.47/0.57    inference(superposition,[],[f85,f335])).
% 1.47/0.57  fof(f378,plain,(
% 1.47/0.57    spl7_30 | spl7_2 | ~spl7_6 | ~spl7_11 | ~spl7_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f361,f172,f162,f137,f117,f375])).
% 1.47/0.57  fof(f361,plain,(
% 1.47/0.57    v1_partfun1(sK5,sK3) | (spl7_2 | ~spl7_6 | ~spl7_11 | ~spl7_13)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f139,f164,f174,f87])).
% 1.47/0.57  fof(f373,plain,(
% 1.47/0.57    spl7_29 | spl7_2 | ~spl7_5 | ~spl7_10 | ~spl7_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f360,f167,f157,f132,f117,f370])).
% 1.47/0.57  fof(f360,plain,(
% 1.47/0.57    v1_partfun1(sK4,sK2) | (spl7_2 | ~spl7_5 | ~spl7_10 | ~spl7_12)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f119,f134,f159,f169,f87])).
% 1.47/0.57  fof(f359,plain,(
% 1.47/0.57    spl7_28 | ~spl7_27),
% 1.47/0.57    inference(avatar_split_clause,[],[f341,f333,f356])).
% 1.47/0.57  fof(f356,plain,(
% 1.47/0.57    spl7_28 <=> v1_funct_1(k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.47/0.57  fof(f341,plain,(
% 1.47/0.57    v1_funct_1(k1_xboole_0) | ~spl7_27),
% 1.47/0.57    inference(superposition,[],[f84,f335])).
% 1.47/0.57  fof(f84,plain,(
% 1.47/0.57    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f57])).
% 1.47/0.57  fof(f354,plain,(
% 1.47/0.57    spl7_3 | spl7_4 | ~spl7_24 | spl7_26),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f353])).
% 1.47/0.57  fof(f353,plain,(
% 1.47/0.57    $false | (spl7_3 | spl7_4 | ~spl7_24 | spl7_26)),
% 1.47/0.57    inference(subsumption_resolution,[],[f315,f349])).
% 1.47/0.57  fof(f349,plain,(
% 1.47/0.57    ~r1_xboole_0(sK3,sK2) | (spl7_3 | spl7_4 | spl7_26)),
% 1.47/0.57    inference(subsumption_resolution,[],[f348,f129])).
% 1.47/0.57  fof(f348,plain,(
% 1.47/0.57    ~r1_xboole_0(sK3,sK2) | v1_xboole_0(sK3) | (spl7_3 | spl7_26)),
% 1.47/0.57    inference(subsumption_resolution,[],[f331,f124])).
% 1.47/0.57  fof(f331,plain,(
% 1.47/0.57    ~r1_xboole_0(sK3,sK2) | v1_xboole_0(sK2) | v1_xboole_0(sK3) | spl7_26),
% 1.47/0.57    inference(resolution,[],[f326,f91])).
% 1.47/0.57  fof(f91,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f58])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.47/0.57    inference(nnf_transformation,[],[f37])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f36])).
% 1.47/0.58  fof(f36,plain,(
% 1.47/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f9])).
% 1.47/0.58  fof(f9,axiom,(
% 1.47/0.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.47/0.58  fof(f326,plain,(
% 1.47/0.58    ~r1_subset_1(sK3,sK2) | spl7_26),
% 1.47/0.58    inference(avatar_component_clause,[],[f324])).
% 1.47/0.58  fof(f324,plain,(
% 1.47/0.58    spl7_26 <=> r1_subset_1(sK3,sK2)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.47/0.58  fof(f347,plain,(
% 1.47/0.58    spl7_25 | ~spl7_27),
% 1.47/0.58    inference(avatar_contradiction_clause,[],[f346])).
% 1.47/0.58  fof(f346,plain,(
% 1.47/0.58    $false | (spl7_25 | ~spl7_27)),
% 1.47/0.58    inference(subsumption_resolution,[],[f338,f319])).
% 1.47/0.58  fof(f319,plain,(
% 1.47/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl7_25),
% 1.47/0.58    inference(avatar_component_clause,[],[f317])).
% 1.47/0.58  fof(f336,plain,(
% 1.47/0.58    spl7_27),
% 1.47/0.58    inference(avatar_split_clause,[],[f328,f333])).
% 1.47/0.58  fof(f328,plain,(
% 1.47/0.58    k1_xboole_0 = sK6(k1_xboole_0)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f82,f84,f83,f85,f81])).
% 1.47/0.58  fof(f81,plain,(
% 1.47/0.58    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f31])).
% 1.47/0.58  fof(f31,plain,(
% 1.47/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.47/0.58    inference(flattening,[],[f30])).
% 1.47/0.58  fof(f30,plain,(
% 1.47/0.58    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f16])).
% 1.47/0.58  fof(f16,axiom,(
% 1.47/0.58    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).
% 1.47/0.58  fof(f327,plain,(
% 1.47/0.58    ~spl7_26 | spl7_3 | spl7_4 | spl7_24),
% 1.47/0.58    inference(avatar_split_clause,[],[f321,f313,f127,f122,f324])).
% 1.47/0.58  fof(f321,plain,(
% 1.47/0.58    ~r1_subset_1(sK3,sK2) | (spl7_3 | spl7_4 | spl7_24)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f129,f124,f314,f90])).
% 1.47/0.58  fof(f90,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f58])).
% 1.47/0.58  fof(f314,plain,(
% 1.47/0.58    ~r1_xboole_0(sK3,sK2) | spl7_24),
% 1.47/0.58    inference(avatar_component_clause,[],[f313])).
% 1.47/0.58  fof(f320,plain,(
% 1.47/0.58    spl7_24 | ~spl7_25 | ~spl7_23),
% 1.47/0.58    inference(avatar_split_clause,[],[f311,f307,f317,f313])).
% 1.47/0.58  fof(f311,plain,(
% 1.47/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | r1_xboole_0(sK3,sK2) | ~spl7_23),
% 1.47/0.58    inference(superposition,[],[f95,f309])).
% 1.47/0.58  fof(f310,plain,(
% 1.47/0.58    spl7_23 | ~spl7_22),
% 1.47/0.58    inference(avatar_split_clause,[],[f298,f294,f307])).
% 1.47/0.58  fof(f298,plain,(
% 1.47/0.58    k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,sK2) | ~spl7_22),
% 1.47/0.58    inference(superposition,[],[f276,f296])).
% 1.47/0.58  fof(f297,plain,(
% 1.47/0.58    spl7_22 | ~spl7_19),
% 1.47/0.58    inference(avatar_split_clause,[],[f291,f212,f294])).
% 1.47/0.58  fof(f291,plain,(
% 1.47/0.58    k1_xboole_0 = k7_relat_1(sK6(sK3),sK2) | ~spl7_19),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f214,f282])).
% 1.47/0.58  fof(f234,plain,(
% 1.47/0.58    spl7_21 | ~spl7_16),
% 1.47/0.58    inference(avatar_split_clause,[],[f229,f195,f231])).
% 1.47/0.58  fof(f231,plain,(
% 1.47/0.58    spl7_21 <=> v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.47/0.58  fof(f195,plain,(
% 1.47/0.58    spl7_16 <=> v1_relat_1(k1_xboole_0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.47/0.58  fof(f229,plain,(
% 1.47/0.58    v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl7_16),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f197,f193,f107])).
% 1.47/0.58  fof(f107,plain,(
% 1.47/0.58    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.47/0.58    inference(equality_resolution,[],[f93])).
% 1.47/0.58  fof(f93,plain,(
% 1.47/0.58    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f59])).
% 1.47/0.58  fof(f193,plain,(
% 1.47/0.58    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f75,f98])).
% 1.47/0.58  fof(f75,plain,(
% 1.47/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f3])).
% 1.47/0.58  fof(f3,axiom,(
% 1.47/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.47/0.58  fof(f197,plain,(
% 1.47/0.58    v1_relat_1(k1_xboole_0) | ~spl7_16),
% 1.47/0.58    inference(avatar_component_clause,[],[f195])).
% 1.47/0.58  fof(f225,plain,(
% 1.47/0.58    spl7_20 | ~spl7_19),
% 1.47/0.58    inference(avatar_split_clause,[],[f216,f212,f222])).
% 1.47/0.58  fof(f216,plain,(
% 1.47/0.58    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl7_19),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f214,f94])).
% 1.47/0.58  fof(f94,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f60])).
% 1.47/0.58  fof(f215,plain,(
% 1.47/0.58    spl7_19 | spl7_3 | spl7_4 | ~spl7_7),
% 1.47/0.58    inference(avatar_split_clause,[],[f204,f142,f127,f122,f212])).
% 1.47/0.58  fof(f142,plain,(
% 1.47/0.58    spl7_7 <=> r1_subset_1(sK2,sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.47/0.58  fof(f204,plain,(
% 1.47/0.58    r1_xboole_0(sK2,sK3) | (spl7_3 | spl7_4 | ~spl7_7)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f124,f129,f144,f90])).
% 1.47/0.58  fof(f144,plain,(
% 1.47/0.58    r1_subset_1(sK2,sK3) | ~spl7_7),
% 1.47/0.58    inference(avatar_component_clause,[],[f142])).
% 1.47/0.58  fof(f210,plain,(
% 1.47/0.58    spl7_18 | ~spl7_13),
% 1.47/0.58    inference(avatar_split_clause,[],[f192,f172,f207])).
% 1.47/0.58  fof(f192,plain,(
% 1.47/0.58    v4_relat_1(sK5,sK3) | ~spl7_13),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f174,f98])).
% 1.47/0.58  fof(f203,plain,(
% 1.47/0.58    spl7_17 | ~spl7_12),
% 1.47/0.58    inference(avatar_split_clause,[],[f191,f167,f200])).
% 1.47/0.58  fof(f191,plain,(
% 1.47/0.58    v4_relat_1(sK4,sK2) | ~spl7_12),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f169,f98])).
% 1.47/0.58  fof(f198,plain,(
% 1.47/0.58    spl7_16),
% 1.47/0.58    inference(avatar_split_clause,[],[f180,f195])).
% 1.47/0.58  fof(f180,plain,(
% 1.47/0.58    v1_relat_1(k1_xboole_0)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f75,f97])).
% 1.47/0.58  fof(f190,plain,(
% 1.47/0.58    spl7_15 | ~spl7_13),
% 1.47/0.58    inference(avatar_split_clause,[],[f179,f172,f187])).
% 1.47/0.58  fof(f179,plain,(
% 1.47/0.58    v1_relat_1(sK5) | ~spl7_13),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f174,f97])).
% 1.47/0.58  fof(f185,plain,(
% 1.47/0.58    spl7_14 | ~spl7_12),
% 1.47/0.58    inference(avatar_split_clause,[],[f178,f167,f182])).
% 1.47/0.58  fof(f178,plain,(
% 1.47/0.58    v1_relat_1(sK4) | ~spl7_12),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f169,f97])).
% 1.47/0.58  fof(f175,plain,(
% 1.47/0.58    spl7_13),
% 1.47/0.58    inference(avatar_split_clause,[],[f73,f172])).
% 1.47/0.58  fof(f73,plain,(
% 1.47/0.58    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f170,plain,(
% 1.47/0.58    spl7_12),
% 1.47/0.58    inference(avatar_split_clause,[],[f70,f167])).
% 1.47/0.58  fof(f70,plain,(
% 1.47/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f165,plain,(
% 1.47/0.58    spl7_11),
% 1.47/0.58    inference(avatar_split_clause,[],[f72,f162])).
% 1.47/0.58  fof(f72,plain,(
% 1.47/0.58    v1_funct_2(sK5,sK3,sK1)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f160,plain,(
% 1.47/0.58    spl7_10),
% 1.47/0.58    inference(avatar_split_clause,[],[f69,f157])).
% 1.47/0.58  fof(f69,plain,(
% 1.47/0.58    v1_funct_2(sK4,sK2,sK1)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f155,plain,(
% 1.47/0.58    spl7_9),
% 1.47/0.58    inference(avatar_split_clause,[],[f66,f152])).
% 1.47/0.58  fof(f66,plain,(
% 1.47/0.58    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f150,plain,(
% 1.47/0.58    spl7_8),
% 1.47/0.58    inference(avatar_split_clause,[],[f64,f147])).
% 1.47/0.58  fof(f64,plain,(
% 1.47/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f145,plain,(
% 1.47/0.58    spl7_7),
% 1.47/0.58    inference(avatar_split_clause,[],[f67,f142])).
% 1.47/0.58  fof(f67,plain,(
% 1.47/0.58    r1_subset_1(sK2,sK3)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f140,plain,(
% 1.47/0.58    spl7_6),
% 1.47/0.58    inference(avatar_split_clause,[],[f71,f137])).
% 1.47/0.58  fof(f71,plain,(
% 1.47/0.58    v1_funct_1(sK5)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f135,plain,(
% 1.47/0.58    spl7_5),
% 1.47/0.58    inference(avatar_split_clause,[],[f68,f132])).
% 1.47/0.58  fof(f68,plain,(
% 1.47/0.58    v1_funct_1(sK4)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f130,plain,(
% 1.47/0.58    ~spl7_4),
% 1.47/0.58    inference(avatar_split_clause,[],[f65,f127])).
% 1.47/0.58  fof(f65,plain,(
% 1.47/0.58    ~v1_xboole_0(sK3)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f125,plain,(
% 1.47/0.58    ~spl7_3),
% 1.47/0.58    inference(avatar_split_clause,[],[f63,f122])).
% 1.47/0.58  fof(f63,plain,(
% 1.47/0.58    ~v1_xboole_0(sK2)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f120,plain,(
% 1.47/0.58    ~spl7_2),
% 1.47/0.58    inference(avatar_split_clause,[],[f62,f117])).
% 1.47/0.58  fof(f62,plain,(
% 1.47/0.58    ~v1_xboole_0(sK1)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  fof(f115,plain,(
% 1.47/0.58    ~spl7_1),
% 1.47/0.58    inference(avatar_split_clause,[],[f61,f112])).
% 1.47/0.58  fof(f61,plain,(
% 1.47/0.58    ~v1_xboole_0(sK0)),
% 1.47/0.58    inference(cnf_transformation,[],[f53])).
% 1.47/0.58  % SZS output end Proof for theBenchmark
% 1.47/0.58  % (20301)------------------------------
% 1.47/0.58  % (20301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (20301)Termination reason: Refutation
% 1.47/0.58  
% 1.47/0.58  % (20301)Memory used [KB]: 2686
% 1.47/0.58  % (20301)Time elapsed: 0.175 s
% 1.47/0.58  % (20301)------------------------------
% 1.47/0.58  % (20301)------------------------------
% 1.47/0.58  % (20293)Success in time 0.223 s
%------------------------------------------------------------------------------
