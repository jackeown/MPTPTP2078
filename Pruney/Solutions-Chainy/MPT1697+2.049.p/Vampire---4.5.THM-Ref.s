%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  290 ( 731 expanded)
%              Number of leaves         :   67 ( 332 expanded)
%              Depth                    :   19
%              Number of atoms          : 1536 (5461 expanded)
%              Number of equality atoms :  239 (1090 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f184,f259,f285,f299,f401,f411,f455,f479,f486,f563,f588,f605,f606,f607,f686,f718,f735,f817,f939,f966,f967,f969,f978,f983,f1005,f1019,f1040,f1098,f1148])).

fof(f1148,plain,
    ( spl6_16
    | spl6_15
    | spl6_14
    | ~ spl6_13
    | spl6_12
    | ~ spl6_11
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f1147,f477,f467,f127,f119,f115,f107,f103,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155])).

fof(f155,plain,
    ( spl6_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f151,plain,
    ( spl6_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f147,plain,
    ( spl6_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f143,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f139,plain,
    ( spl6_12
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f135,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f123,plain,
    ( spl6_8
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f111,plain,
    ( spl6_5
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f103,plain,
    ( spl6_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f107,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f115,plain,
    ( spl6_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f119,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f127,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f467,plain,
    ( spl6_66
  <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f477,plain,
    ( spl6_68
  <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1147,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(trivial_inequality_removal,[],[f1146])).

fof(f1146,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1145,f1048])).

fof(f1048,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f477])).

fof(f1145,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1144,f456])).

fof(f456,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f321,f120])).

fof(f120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f321,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5) )
    | ~ spl6_9 ),
    inference(resolution,[],[f87,f128])).

fof(f128,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f1144,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1143,f1048])).

fof(f1143,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f1142,f1023])).

fof(f1023,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f467])).

fof(f1142,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f1141,f441])).

fof(f441,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f320,f108])).

fof(f108,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f320,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f87,f116])).

fof(f116,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1141,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(trivial_inequality_removal,[],[f1140])).

fof(f1140,plain,
    ( sK5 != sK5
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(superposition,[],[f104,f163])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
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
    inference(subsumption_resolution,[],[f161,f88])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f161,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
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
    inference(subsumption_resolution,[],[f159,f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
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
    inference(subsumption_resolution,[],[f93,f90])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f104,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1098,plain,
    ( spl6_16
    | spl6_15
    | spl6_14
    | ~ spl6_13
    | spl6_12
    | ~ spl6_11
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f1091,f477,f467,f127,f119,f115,f107,f100,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155])).

fof(f100,plain,
    ( spl6_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1091,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(trivial_inequality_removal,[],[f1090])).

fof(f1090,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1089,f1048])).

fof(f1089,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1088,f456])).

fof(f1088,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1087,f1048])).

fof(f1087,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f1086,f1023])).

fof(f1086,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f1085,f441])).

fof(f1085,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f1084])).

fof(f1084,plain,
    ( sK4 != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(superposition,[],[f101,f162])).

fof(f162,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
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
    inference(subsumption_resolution,[],[f160,f88])).

fof(f160,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
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
    inference(subsumption_resolution,[],[f158,f89])).

fof(f158,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
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
    inference(subsumption_resolution,[],[f94,f90])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1040,plain,
    ( ~ spl6_11
    | ~ spl6_18
    | spl6_68
    | ~ spl6_133 ),
    inference(avatar_split_clause,[],[f1039,f976,f477,f180,f135])).

fof(f180,plain,
    ( spl6_18
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f976,plain,
    ( spl6_133
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f1039,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_68
    | ~ spl6_133 ),
    inference(trivial_inequality_removal,[],[f1038])).

fof(f1038,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_68
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f1037,f1007])).

fof(f1007,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_133 ),
    inference(avatar_component_clause,[],[f976])).

fof(f1037,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_68 ),
    inference(forward_demodulation,[],[f1034,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1034,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_68 ),
    inference(superposition,[],[f478,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f478,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_68 ),
    inference(avatar_component_clause,[],[f477])).

fof(f1019,plain,
    ( ~ spl6_11
    | ~ spl6_65
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_18
    | spl6_64 ),
    inference(avatar_split_clause,[],[f1018,f453,f180,f127,f119,f459,f135])).

fof(f459,plain,
    ( spl6_65
  <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f453,plain,
    ( spl6_64
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f1018,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_18
    | spl6_64 ),
    inference(forward_demodulation,[],[f465,f456])).

fof(f465,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_64 ),
    inference(forward_demodulation,[],[f463,f181])).

fof(f463,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_64 ),
    inference(superposition,[],[f454,f84])).

fof(f454,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_64 ),
    inference(avatar_component_clause,[],[f453])).

fof(f1005,plain,
    ( ~ spl6_53
    | ~ spl6_54
    | spl6_133 ),
    inference(avatar_split_clause,[],[f1004,f976,f386,f383])).

fof(f383,plain,
    ( spl6_53
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f386,plain,
    ( spl6_54
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f1004,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_133 ),
    inference(trivial_inequality_removal,[],[f1003])).

fof(f1003,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_133 ),
    inference(superposition,[],[f977,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f977,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_133 ),
    inference(avatar_component_clause,[],[f976])).

fof(f983,plain,
    ( ~ spl6_11
    | ~ spl6_18
    | spl6_69
    | ~ spl6_131 ),
    inference(avatar_split_clause,[],[f982,f937,f484,f180,f135])).

fof(f484,plain,
    ( spl6_69
  <=> k1_xboole_0 = k3_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f937,plain,
    ( spl6_131
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

% (19185)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f982,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_69
    | ~ spl6_131 ),
    inference(trivial_inequality_removal,[],[f981])).

fof(f981,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_69
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f489,f962])).

fof(f962,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl6_131 ),
    inference(trivial_inequality_removal,[],[f958])).

fof(f958,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )
    | ~ spl6_131 ),
    inference(superposition,[],[f943,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f943,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k3_xboole_0(X1,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) )
    | ~ spl6_131 ),
    inference(resolution,[],[f938,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f938,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )
    | ~ spl6_131 ),
    inference(avatar_component_clause,[],[f937])).

fof(f489,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_69 ),
    inference(forward_demodulation,[],[f488,f181])).

fof(f488,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_69 ),
    inference(superposition,[],[f485,f84])).

fof(f485,plain,
    ( k1_xboole_0 != k3_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | spl6_69 ),
    inference(avatar_component_clause,[],[f484])).

fof(f978,plain,
    ( ~ spl6_31
    | ~ spl6_133
    | ~ spl6_100
    | spl6_65
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f974,f598,f459,f648,f976,f264])).

fof(f264,plain,
    ( spl6_31
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f648,plain,
    ( spl6_100
  <=> r1_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f598,plain,
    ( spl6_91
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f974,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK3)
    | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_relat_1(sK5)
    | spl6_65
    | ~ spl6_91 ),
    inference(forward_demodulation,[],[f462,f599])).

fof(f599,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f598])).

fof(f462,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_65 ),
    inference(superposition,[],[f460,f73])).

fof(f460,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl6_65 ),
    inference(avatar_component_clause,[],[f459])).

fof(f969,plain,
    ( sK3 != k1_relat_1(sK5)
    | r1_xboole_0(k1_xboole_0,sK3)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f967,plain,
    ( spl6_59
    | ~ spl6_131 ),
    inference(avatar_contradiction_clause,[],[f964])).

fof(f964,plain,
    ( $false
    | spl6_59
    | ~ spl6_131 ),
    inference(subsumption_resolution,[],[f410,f962])).

fof(f410,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | spl6_59 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl6_59
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f966,plain,
    ( spl6_39
    | ~ spl6_131 ),
    inference(avatar_contradiction_clause,[],[f963])).

fof(f963,plain,
    ( $false
    | spl6_39
    | ~ spl6_131 ),
    inference(subsumption_resolution,[],[f298,f962])).

fof(f298,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl6_39
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f939,plain,
    ( ~ spl6_80
    | spl6_131
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f935,f270,f937,f543])).

fof(f543,plain,
    ( spl6_80
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f270,plain,
    ( spl6_33
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f935,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f934,f271])).

fof(f271,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f270])).

fof(f934,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f930,f271])).

fof(f930,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_33 ),
    inference(superposition,[],[f836,f73])).

fof(f836,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl6_33 ),
    inference(superposition,[],[f210,f271])).

fof(f210,plain,(
    ! [X2] : k1_relat_1(k7_relat_1(k1_xboole_0,X2)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X2) ),
    inference(resolution,[],[f166,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f76,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f817,plain,
    ( spl6_15
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f815,f601,f107,f111,f151])).

fof(f601,plain,
    ( spl6_92
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK5,sK3,X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f815,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_4
    | ~ spl6_92 ),
    inference(resolution,[],[f602,f108])).

fof(f602,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
        | ~ v1_funct_2(sK5,sK3,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f601])).

fof(f735,plain,
    ( ~ spl6_27
    | spl6_110 ),
    inference(avatar_split_clause,[],[f730,f716,f243])).

fof(f243,plain,
    ( spl6_27
  <=> k1_xboole_0 = k3_xboole_0(sK2,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f716,plain,
    ( spl6_110
  <=> r1_xboole_0(sK2,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f730,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k1_relat_1(sK5))
    | spl6_110 ),
    inference(resolution,[],[f717,f83])).

fof(f717,plain,
    ( ~ r1_xboole_0(sK2,k1_relat_1(sK5))
    | spl6_110 ),
    inference(avatar_component_clause,[],[f716])).

fof(f718,plain,
    ( ~ spl6_31
    | ~ spl6_110
    | spl6_33
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f713,f246,f270,f716,f264])).

fof(f246,plain,
    ( spl6_28
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f713,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_xboole_0(sK2,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ spl6_28 ),
    inference(superposition,[],[f247,f73])).

fof(f247,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK2))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f246])).

fof(f686,plain,
    ( spl6_91
    | spl6_92
    | ~ spl6_4
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f596,f583,f107,f601,f598])).

fof(f583,plain,
    ( spl6_87
  <=> ! [X3,X2,X4] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | k1_relat_1(sK5) = X2
        | ~ v1_funct_2(sK5,X2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f596,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
        | sK3 = k1_relat_1(sK5)
        | ~ v1_funct_2(sK5,sK3,X0) )
    | ~ spl6_4
    | ~ spl6_87 ),
    inference(resolution,[],[f584,f108])).

fof(f584,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | k1_relat_1(sK5) = X2
        | ~ v1_funct_2(sK5,X2,X4) )
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f583])).

fof(f607,plain,
    ( sK3 != k1_relat_1(sK5)
    | k1_xboole_0 != k3_xboole_0(sK2,sK3)
    | k1_xboole_0 = k3_xboole_0(sK2,k1_relat_1(sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f606,plain,
    ( sK3 != k1_relat_1(sK5)
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_relat_1(sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f605,plain,
    ( ~ spl6_4
    | ~ spl6_88 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f108,f587])).

fof(f587,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl6_88
  <=> ! [X1,X0] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f588,plain,
    ( spl6_87
    | spl6_88
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f579,f115,f586,f583])).

fof(f579,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(sK5,X2,X4)
        | k1_relat_1(sK5) = X2
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | v1_xboole_0(X4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f578,f116])).

fof(f578,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X8)))
      | ~ v1_funct_2(X4,X5,X9)
      | k1_relat_1(X4) = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X9)))
      | v1_xboole_0(X9) ) ),
    inference(resolution,[],[f576,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f576,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f167,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f80,f85])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f563,plain,(
    spl6_80 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | spl6_80 ),
    inference(resolution,[],[f559,f68])).

fof(f559,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_80 ),
    inference(resolution,[],[f544,f85])).

fof(f544,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_80 ),
    inference(avatar_component_clause,[],[f543])).

fof(f486,plain,
    ( ~ spl6_69
    | spl6_67 ),
    inference(avatar_split_clause,[],[f481,f474,f484])).

fof(f474,plain,
    ( spl6_67
  <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f481,plain,
    ( k1_xboole_0 != k3_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | spl6_67 ),
    inference(resolution,[],[f475,f83])).

fof(f475,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | spl6_67 ),
    inference(avatar_component_clause,[],[f474])).

fof(f479,plain,
    ( ~ spl6_31
    | ~ spl6_67
    | ~ spl6_68
    | spl6_66 ),
    inference(avatar_split_clause,[],[f471,f467,f477,f474,f264])).

fof(f471,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_66 ),
    inference(superposition,[],[f468,f73])).

fof(f468,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | spl6_66 ),
    inference(avatar_component_clause,[],[f467])).

fof(f455,plain,
    ( ~ spl6_64
    | spl6_1
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f445,f115,f107,f97,f453])).

fof(f97,plain,
    ( spl6_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f445,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(superposition,[],[f98,f441])).

fof(f98,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f411,plain,
    ( ~ spl6_59
    | spl6_54 ),
    inference(avatar_split_clause,[],[f403,f386,f409])).

fof(f403,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | spl6_54 ),
    inference(resolution,[],[f387,f83])).

fof(f387,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f386])).

fof(f401,plain,
    ( ~ spl6_7
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl6_7
    | spl6_53 ),
    inference(subsumption_resolution,[],[f120,f399])).

fof(f399,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_53 ),
    inference(resolution,[],[f384,f85])).

fof(f384,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_53 ),
    inference(avatar_component_clause,[],[f383])).

fof(f299,plain,
    ( ~ spl6_39
    | spl6_32 ),
    inference(avatar_split_clause,[],[f288,f267,f297])).

fof(f267,plain,
    ( spl6_32
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f288,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | spl6_32 ),
    inference(resolution,[],[f268,f83])).

fof(f268,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f267])).

fof(f285,plain,
    ( ~ spl6_4
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl6_4
    | spl6_31 ),
    inference(subsumption_resolution,[],[f108,f283])).

fof(f283,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_31 ),
    inference(resolution,[],[f265,f85])).

fof(f265,plain,
    ( ~ v1_relat_1(sK5)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f264])).

fof(f259,plain,
    ( ~ spl6_27
    | spl6_23
    | spl6_28
    | ~ spl6_4
    | spl6_14 ),
    inference(avatar_split_clause,[],[f219,f147,f107,f246,f229,f243])).

fof(f229,plain,
    ( spl6_23
  <=> v1_xboole_0(k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f219,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK2))
    | v1_xboole_0(k1_relat_1(sK5))
    | k1_xboole_0 != k3_xboole_0(sK2,k1_relat_1(sK5))
    | ~ spl6_4
    | spl6_14 ),
    inference(superposition,[],[f204,f208])).

fof(f208,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(k1_relat_1(sK5),X0)
    | ~ spl6_4 ),
    inference(resolution,[],[f166,f108])).

fof(f204,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k3_xboole_0(X2,sK2)
        | v1_xboole_0(X2)
        | k1_xboole_0 != k3_xboole_0(sK2,X2) )
    | spl6_14 ),
    inference(resolution,[],[f200,f148])).

fof(f148,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f200,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X3)
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | v1_xboole_0(X2)
      | k1_xboole_0 != k3_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f194,f83])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f177,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f177,plain,(
    ! [X2,X3] :
      ( ~ r1_subset_1(X2,X3)
      | v1_xboole_0(X3)
      | k1_xboole_0 = k3_xboole_0(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | v1_xboole_0(X3)
      | k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_subset_1(X2,X3)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f165,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f184,plain,
    ( spl6_18
    | spl6_14
    | spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f174,f131,f139,f147,f180])).

fof(f131,plain,
    ( spl6_10
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f174,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f165,f132])).

fof(f132,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f157,plain,(
    ~ spl6_16 ),
    inference(avatar_split_clause,[],[f54,f155])).

fof(f54,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f47,f46,f45,f44,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f18])).

% (19170)Refutation not found, incomplete strategy% (19170)------------------------------
% (19170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f153,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f55,f151])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f149,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f56,f147])).

fof(f56,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f145,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f57,f143])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f141,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f58,f139])).

fof(f58,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f137,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f59,f135])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f133,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f60,f131])).

fof(f60,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f129,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f61,f127])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f125,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f62,f123])).

fof(f62,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f121,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f64,f115])).

fof(f64,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f113,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f65,f111])).

fof(f65,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f66,f107])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f67,f103,f100,f97])).

fof(f67,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:17:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (19177)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (19170)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (19175)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (19186)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (19171)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (19183)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (19171)Refutation not found, incomplete strategy% (19171)------------------------------
% 0.22/0.50  % (19171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19174)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (19172)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (19176)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (19189)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (19178)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (19171)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19171)Memory used [KB]: 10746
% 0.22/0.52  % (19171)Time elapsed: 0.065 s
% 0.22/0.52  % (19171)------------------------------
% 0.22/0.52  % (19171)------------------------------
% 0.22/0.52  % (19173)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (19184)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (19180)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (19187)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (19181)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (19182)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (19179)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (19190)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % (19190)Refutation not found, incomplete strategy% (19190)------------------------------
% 0.22/0.54  % (19190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19190)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (19190)Memory used [KB]: 10618
% 0.22/0.54  % (19190)Time elapsed: 0.112 s
% 0.22/0.54  % (19190)------------------------------
% 0.22/0.54  % (19190)------------------------------
% 0.22/0.54  % (19188)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (19176)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1149,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f184,f259,f285,f299,f401,f411,f455,f479,f486,f563,f588,f605,f606,f607,f686,f718,f735,f817,f939,f966,f967,f969,f978,f983,f1005,f1019,f1040,f1098,f1148])).
% 0.22/0.54  fof(f1148,plain,(
% 0.22/0.54    spl6_16 | spl6_15 | spl6_14 | ~spl6_13 | spl6_12 | ~spl6_11 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68),
% 0.22/0.54    inference(avatar_split_clause,[],[f1147,f477,f467,f127,f119,f115,f107,f103,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl6_16 <=> v1_xboole_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl6_15 <=> v1_xboole_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    spl6_14 <=> v1_xboole_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    spl6_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    spl6_12 <=> v1_xboole_0(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    spl6_8 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl6_5 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl6_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl6_4 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    spl6_6 <=> v1_funct_1(sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    spl6_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    spl6_9 <=> v1_funct_1(sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.54  fof(f467,plain,(
% 0.22/0.54    spl6_66 <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.22/0.54  fof(f477,plain,(
% 0.22/0.54    spl6_68 <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.22/0.54  fof(f1147,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f1146])).
% 0.22/0.54  fof(f1146,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1145,f1048])).
% 0.22/0.54  fof(f1048,plain,(
% 0.22/0.54    k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_68),
% 0.22/0.54    inference(avatar_component_clause,[],[f477])).
% 0.22/0.54  fof(f1145,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1144,f456])).
% 0.22/0.54  fof(f456,plain,(
% 0.22/0.54    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | (~spl6_7 | ~spl6_9)),
% 0.22/0.54    inference(resolution,[],[f321,f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f119])).
% 0.22/0.54  fof(f321,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5)) ) | ~spl6_9),
% 0.22/0.54    inference(resolution,[],[f87,f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    v1_funct_1(sK4) | ~spl6_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f127])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.54  fof(f1144,plain,(
% 0.22/0.54    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1143,f1048])).
% 0.22/0.54  fof(f1143,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_66)),
% 0.22/0.54    inference(forward_demodulation,[],[f1142,f1023])).
% 0.22/0.54  fof(f1023,plain,(
% 0.22/0.54    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_66),
% 0.22/0.54    inference(avatar_component_clause,[],[f467])).
% 0.22/0.54  fof(f1142,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f1141,f441])).
% 0.22/0.54  fof(f441,plain,(
% 0.22/0.54    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) ) | (~spl6_4 | ~spl6_6)),
% 0.22/0.54    inference(resolution,[],[f320,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f107])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2)) ) | ~spl6_6),
% 0.22/0.54    inference(resolution,[],[f87,f116])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    v1_funct_1(sK5) | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f115])).
% 0.22/0.54  fof(f1141,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f1140])).
% 0.22/0.54  fof(f1140,plain,(
% 0.22/0.54    sK5 != sK5 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 0.22/0.54    inference(superposition,[],[f104,f163])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f161,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f159,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f93,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f103])).
% 0.22/0.54  fof(f1098,plain,(
% 0.22/0.54    spl6_16 | spl6_15 | spl6_14 | ~spl6_13 | spl6_12 | ~spl6_11 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68),
% 0.22/0.54    inference(avatar_split_clause,[],[f1091,f477,f467,f127,f119,f115,f107,f100,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl6_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f1091,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f1090])).
% 0.22/0.54  fof(f1090,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1089,f1048])).
% 0.22/0.54  fof(f1089,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1088,f456])).
% 0.22/0.54  fof(f1088,plain,(
% 0.22/0.54    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_66 | ~spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1087,f1048])).
% 0.22/0.54  fof(f1087,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_66)),
% 0.22/0.54    inference(forward_demodulation,[],[f1086,f1023])).
% 0.22/0.54  fof(f1086,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f1085,f441])).
% 0.22/0.54  fof(f1085,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f1084])).
% 0.22/0.54  fof(f1084,plain,(
% 0.22/0.54    sK4 != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 0.22/0.54    inference(superposition,[],[f101,f162])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f160,f88])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f158,f89])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f94,f90])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f100])).
% 0.22/0.54  fof(f1040,plain,(
% 0.22/0.54    ~spl6_11 | ~spl6_18 | spl6_68 | ~spl6_133),
% 0.22/0.54    inference(avatar_split_clause,[],[f1039,f976,f477,f180,f135])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    spl6_18 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.54  fof(f976,plain,(
% 0.22/0.54    spl6_133 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).
% 0.22/0.54  fof(f1039,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_68 | ~spl6_133)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f1038])).
% 0.22/0.54  fof(f1038,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_68 | ~spl6_133)),
% 0.22/0.54    inference(forward_demodulation,[],[f1037,f1007])).
% 0.22/0.54  fof(f1007,plain,(
% 0.22/0.54    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_133),
% 0.22/0.54    inference(avatar_component_clause,[],[f976])).
% 0.22/0.54  fof(f1037,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_68)),
% 0.22/0.54    inference(forward_demodulation,[],[f1034,f181])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f180])).
% 0.22/0.54  fof(f1034,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_68),
% 0.22/0.54    inference(superposition,[],[f478,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.54  fof(f478,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | spl6_68),
% 0.22/0.54    inference(avatar_component_clause,[],[f477])).
% 0.22/0.54  fof(f1019,plain,(
% 0.22/0.54    ~spl6_11 | ~spl6_65 | ~spl6_7 | ~spl6_9 | ~spl6_18 | spl6_64),
% 0.22/0.54    inference(avatar_split_clause,[],[f1018,f453,f180,f127,f119,f459,f135])).
% 0.22/0.54  fof(f459,plain,(
% 0.22/0.54    spl6_65 <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.22/0.54  fof(f453,plain,(
% 0.22/0.54    spl6_64 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.22/0.54  fof(f1018,plain,(
% 0.22/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_9 | ~spl6_18 | spl6_64)),
% 0.22/0.54    inference(forward_demodulation,[],[f465,f456])).
% 0.22/0.54  fof(f465,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_64)),
% 0.22/0.54    inference(forward_demodulation,[],[f463,f181])).
% 0.22/0.54  fof(f463,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_64),
% 0.22/0.54    inference(superposition,[],[f454,f84])).
% 0.22/0.54  fof(f454,plain,(
% 0.22/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_64),
% 0.22/0.54    inference(avatar_component_clause,[],[f453])).
% 0.22/0.54  fof(f1005,plain,(
% 0.22/0.54    ~spl6_53 | ~spl6_54 | spl6_133),
% 0.22/0.54    inference(avatar_split_clause,[],[f1004,f976,f386,f383])).
% 0.22/0.54  fof(f383,plain,(
% 0.22/0.54    spl6_53 <=> v1_relat_1(sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.22/0.54  fof(f386,plain,(
% 0.22/0.54    spl6_54 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.22/0.54  fof(f1004,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_133),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f1003])).
% 0.22/0.54  fof(f1003,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_133),
% 0.22/0.54    inference(superposition,[],[f977,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.22/0.54  fof(f977,plain,(
% 0.22/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl6_133),
% 0.22/0.54    inference(avatar_component_clause,[],[f976])).
% 0.22/0.54  fof(f983,plain,(
% 0.22/0.54    ~spl6_11 | ~spl6_18 | spl6_69 | ~spl6_131),
% 0.22/0.54    inference(avatar_split_clause,[],[f982,f937,f484,f180,f135])).
% 0.22/0.54  fof(f484,plain,(
% 0.22/0.54    spl6_69 <=> k1_xboole_0 = k3_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 0.22/0.54  fof(f937,plain,(
% 0.22/0.54    spl6_131 <=> ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).
% 0.22/0.55  % (19185)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.55  fof(f982,plain,(
% 0.22/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_69 | ~spl6_131)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f981])).
% 0.22/0.55  fof(f981,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_69 | ~spl6_131)),
% 0.22/0.55    inference(forward_demodulation,[],[f489,f962])).
% 0.22/0.55  fof(f962,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_131),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f958])).
% 0.22/0.55  fof(f958,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_131),
% 0.22/0.55    inference(superposition,[],[f943,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.55  fof(f943,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k3_xboole_0(X1,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl6_131),
% 0.22/0.55    inference(resolution,[],[f938,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.55  fof(f938,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_131),
% 0.22/0.55    inference(avatar_component_clause,[],[f937])).
% 0.22/0.55  fof(f489,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_69)),
% 0.22/0.55    inference(forward_demodulation,[],[f488,f181])).
% 0.22/0.55  fof(f488,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK2,sK3),k1_relat_1(sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_69),
% 0.22/0.55    inference(superposition,[],[f485,f84])).
% 0.22/0.55  fof(f485,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | spl6_69),
% 0.22/0.55    inference(avatar_component_clause,[],[f484])).
% 0.22/0.55  fof(f978,plain,(
% 0.22/0.55    ~spl6_31 | ~spl6_133 | ~spl6_100 | spl6_65 | ~spl6_91),
% 0.22/0.55    inference(avatar_split_clause,[],[f974,f598,f459,f648,f976,f264])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    spl6_31 <=> v1_relat_1(sK5)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.55  fof(f648,plain,(
% 0.22/0.55    spl6_100 <=> r1_xboole_0(k1_xboole_0,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 0.22/0.55  fof(f598,plain,(
% 0.22/0.55    spl6_91 <=> sK3 = k1_relat_1(sK5)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 0.22/0.55  fof(f974,plain,(
% 0.22/0.55    ~r1_xboole_0(k1_xboole_0,sK3) | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~v1_relat_1(sK5) | (spl6_65 | ~spl6_91)),
% 0.22/0.55    inference(forward_demodulation,[],[f462,f599])).
% 0.22/0.55  fof(f599,plain,(
% 0.22/0.55    sK3 = k1_relat_1(sK5) | ~spl6_91),
% 0.22/0.55    inference(avatar_component_clause,[],[f598])).
% 0.22/0.55  fof(f462,plain,(
% 0.22/0.55    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_65),
% 0.22/0.55    inference(superposition,[],[f460,f73])).
% 0.22/0.55  fof(f460,plain,(
% 0.22/0.55    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl6_65),
% 0.22/0.55    inference(avatar_component_clause,[],[f459])).
% 0.22/0.55  fof(f969,plain,(
% 0.22/0.55    sK3 != k1_relat_1(sK5) | r1_xboole_0(k1_xboole_0,sK3) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f967,plain,(
% 0.22/0.55    spl6_59 | ~spl6_131),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f964])).
% 0.22/0.55  fof(f964,plain,(
% 0.22/0.55    $false | (spl6_59 | ~spl6_131)),
% 0.22/0.55    inference(subsumption_resolution,[],[f410,f962])).
% 0.22/0.55  fof(f410,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | spl6_59),
% 0.22/0.55    inference(avatar_component_clause,[],[f409])).
% 0.22/0.55  fof(f409,plain,(
% 0.22/0.55    spl6_59 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.22/0.55  fof(f966,plain,(
% 0.22/0.55    spl6_39 | ~spl6_131),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f963])).
% 0.22/0.55  fof(f963,plain,(
% 0.22/0.55    $false | (spl6_39 | ~spl6_131)),
% 0.22/0.55    inference(subsumption_resolution,[],[f298,f962])).
% 0.22/0.55  fof(f298,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | spl6_39),
% 0.22/0.55    inference(avatar_component_clause,[],[f297])).
% 0.22/0.55  fof(f297,plain,(
% 0.22/0.55    spl6_39 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.55  fof(f939,plain,(
% 0.22/0.55    ~spl6_80 | spl6_131 | ~spl6_33),
% 0.22/0.55    inference(avatar_split_clause,[],[f935,f270,f937,f543])).
% 0.22/0.55  fof(f543,plain,(
% 0.22/0.55    spl6_80 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 0.22/0.55  fof(f270,plain,(
% 0.22/0.55    spl6_33 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.55  fof(f935,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_33),
% 0.22/0.55    inference(forward_demodulation,[],[f934,f271])).
% 0.22/0.55  fof(f271,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_33),
% 0.22/0.55    inference(avatar_component_clause,[],[f270])).
% 0.22/0.55  fof(f934,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) | ~r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_33),
% 0.22/0.55    inference(forward_demodulation,[],[f930,f271])).
% 0.22/0.55  fof(f930,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) | ~r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_33),
% 0.22/0.55    inference(superposition,[],[f836,f73])).
% 0.22/0.55  fof(f836,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl6_33),
% 0.22/0.55    inference(superposition,[],[f210,f271])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    ( ! [X2] : (k1_relat_1(k7_relat_1(k1_xboole_0,X2)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X2)) )),
% 0.22/0.55    inference(resolution,[],[f166,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)) )),
% 0.22/0.55    inference(resolution,[],[f76,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.55  fof(f817,plain,(
% 0.22/0.55    spl6_15 | ~spl6_5 | ~spl6_4 | ~spl6_92),
% 0.22/0.55    inference(avatar_split_clause,[],[f815,f601,f107,f111,f151])).
% 0.22/0.55  fof(f601,plain,(
% 0.22/0.55    spl6_92 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK5,sK3,X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 0.22/0.55  fof(f815,plain,(
% 0.22/0.55    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | (~spl6_4 | ~spl6_92)),
% 0.22/0.55    inference(resolution,[],[f602,f108])).
% 0.22/0.55  fof(f602,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_2(sK5,sK3,X0) | v1_xboole_0(X0)) ) | ~spl6_92),
% 0.22/0.55    inference(avatar_component_clause,[],[f601])).
% 0.22/0.55  fof(f735,plain,(
% 0.22/0.55    ~spl6_27 | spl6_110),
% 0.22/0.55    inference(avatar_split_clause,[],[f730,f716,f243])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    spl6_27 <=> k1_xboole_0 = k3_xboole_0(sK2,k1_relat_1(sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.55  fof(f716,plain,(
% 0.22/0.55    spl6_110 <=> r1_xboole_0(sK2,k1_relat_1(sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 0.22/0.55  fof(f730,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(sK2,k1_relat_1(sK5)) | spl6_110),
% 0.22/0.55    inference(resolution,[],[f717,f83])).
% 0.22/0.55  fof(f717,plain,(
% 0.22/0.55    ~r1_xboole_0(sK2,k1_relat_1(sK5)) | spl6_110),
% 0.22/0.55    inference(avatar_component_clause,[],[f716])).
% 0.22/0.55  fof(f718,plain,(
% 0.22/0.55    ~spl6_31 | ~spl6_110 | spl6_33 | ~spl6_28),
% 0.22/0.55    inference(avatar_split_clause,[],[f713,f246,f270,f716,f264])).
% 0.22/0.55  fof(f246,plain,(
% 0.22/0.55    spl6_28 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.55  fof(f713,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_xboole_0(sK2,k1_relat_1(sK5)) | ~v1_relat_1(sK5) | ~spl6_28),
% 0.22/0.55    inference(superposition,[],[f247,f73])).
% 0.22/0.55  fof(f247,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK2)) | ~spl6_28),
% 0.22/0.55    inference(avatar_component_clause,[],[f246])).
% 0.22/0.55  fof(f686,plain,(
% 0.22/0.55    spl6_91 | spl6_92 | ~spl6_4 | ~spl6_87),
% 0.22/0.55    inference(avatar_split_clause,[],[f596,f583,f107,f601,f598])).
% 0.22/0.55  fof(f583,plain,(
% 0.22/0.55    spl6_87 <=> ! [X3,X2,X4] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | k1_relat_1(sK5) = X2 | ~v1_funct_2(sK5,X2,X4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 0.22/0.55  fof(f596,plain,(
% 0.22/0.55    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | sK3 = k1_relat_1(sK5) | ~v1_funct_2(sK5,sK3,X0)) ) | (~spl6_4 | ~spl6_87)),
% 0.22/0.55    inference(resolution,[],[f584,f108])).
% 0.22/0.55  fof(f584,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | k1_relat_1(sK5) = X2 | ~v1_funct_2(sK5,X2,X4)) ) | ~spl6_87),
% 0.22/0.55    inference(avatar_component_clause,[],[f583])).
% 0.22/0.55  fof(f607,plain,(
% 0.22/0.55    sK3 != k1_relat_1(sK5) | k1_xboole_0 != k3_xboole_0(sK2,sK3) | k1_xboole_0 = k3_xboole_0(sK2,k1_relat_1(sK5))),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f606,plain,(
% 0.22/0.55    sK3 != k1_relat_1(sK5) | v1_xboole_0(sK3) | ~v1_xboole_0(k1_relat_1(sK5))),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f605,plain,(
% 0.22/0.55    ~spl6_4 | ~spl6_88),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f604])).
% 0.22/0.55  fof(f604,plain,(
% 0.22/0.55    $false | (~spl6_4 | ~spl6_88)),
% 0.22/0.55    inference(subsumption_resolution,[],[f108,f587])).
% 0.22/0.55  fof(f587,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_88),
% 0.22/0.55    inference(avatar_component_clause,[],[f586])).
% 0.22/0.55  fof(f586,plain,(
% 0.22/0.55    spl6_88 <=> ! [X1,X0] : ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 0.22/0.55  fof(f588,plain,(
% 0.22/0.55    spl6_87 | spl6_88 | ~spl6_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f579,f115,f586,f583])).
% 0.22/0.55  fof(f579,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK5,X2,X4) | k1_relat_1(sK5) = X2 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | v1_xboole_0(X4)) ) | ~spl6_6),
% 0.22/0.55    inference(resolution,[],[f578,f116])).
% 0.22/0.55  fof(f578,plain,(
% 0.22/0.55    ( ! [X6,X4,X8,X7,X5,X9] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X8))) | ~v1_funct_2(X4,X5,X9) | k1_relat_1(X4) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X9))) | v1_xboole_0(X9)) )),
% 0.22/0.55    inference(resolution,[],[f576,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(flattening,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.55  fof(f576,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.22/0.55    inference(resolution,[],[f167,f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.22/0.55    inference(resolution,[],[f80,f85])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.55  fof(f563,plain,(
% 0.22/0.55    spl6_80),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f562])).
% 0.22/0.55  fof(f562,plain,(
% 0.22/0.55    $false | spl6_80),
% 0.22/0.55    inference(resolution,[],[f559,f68])).
% 0.22/0.55  fof(f559,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_80),
% 0.22/0.55    inference(resolution,[],[f544,f85])).
% 0.22/0.55  fof(f544,plain,(
% 0.22/0.55    ~v1_relat_1(k1_xboole_0) | spl6_80),
% 0.22/0.55    inference(avatar_component_clause,[],[f543])).
% 0.22/0.55  fof(f486,plain,(
% 0.22/0.55    ~spl6_69 | spl6_67),
% 0.22/0.55    inference(avatar_split_clause,[],[f481,f474,f484])).
% 0.22/0.55  fof(f474,plain,(
% 0.22/0.55    spl6_67 <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.22/0.55  fof(f481,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | spl6_67),
% 0.22/0.55    inference(resolution,[],[f475,f83])).
% 0.22/0.55  fof(f475,plain,(
% 0.22/0.55    ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | spl6_67),
% 0.22/0.55    inference(avatar_component_clause,[],[f474])).
% 0.22/0.55  fof(f479,plain,(
% 0.22/0.55    ~spl6_31 | ~spl6_67 | ~spl6_68 | spl6_66),
% 0.22/0.55    inference(avatar_split_clause,[],[f471,f467,f477,f474,f264])).
% 0.22/0.55  fof(f471,plain,(
% 0.22/0.55    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_66),
% 0.22/0.55    inference(superposition,[],[f468,f73])).
% 0.22/0.55  fof(f468,plain,(
% 0.22/0.55    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | spl6_66),
% 0.22/0.55    inference(avatar_component_clause,[],[f467])).
% 0.22/0.55  fof(f455,plain,(
% 0.22/0.55    ~spl6_64 | spl6_1 | ~spl6_4 | ~spl6_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f445,f115,f107,f97,f453])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl6_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.55  fof(f445,plain,(
% 0.22/0.55    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_4 | ~spl6_6)),
% 0.22/0.55    inference(superposition,[],[f98,f441])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f97])).
% 0.22/0.55  fof(f411,plain,(
% 0.22/0.55    ~spl6_59 | spl6_54),
% 0.22/0.55    inference(avatar_split_clause,[],[f403,f386,f409])).
% 0.22/0.55  fof(f403,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | spl6_54),
% 0.22/0.55    inference(resolution,[],[f387,f83])).
% 0.22/0.55  fof(f387,plain,(
% 0.22/0.55    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | spl6_54),
% 0.22/0.55    inference(avatar_component_clause,[],[f386])).
% 0.22/0.55  fof(f401,plain,(
% 0.22/0.55    ~spl6_7 | spl6_53),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f400])).
% 0.22/0.55  fof(f400,plain,(
% 0.22/0.55    $false | (~spl6_7 | spl6_53)),
% 0.22/0.55    inference(subsumption_resolution,[],[f120,f399])).
% 0.22/0.55  fof(f399,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_53),
% 0.22/0.55    inference(resolution,[],[f384,f85])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    ~v1_relat_1(sK4) | spl6_53),
% 0.22/0.55    inference(avatar_component_clause,[],[f383])).
% 0.22/0.55  fof(f299,plain,(
% 0.22/0.55    ~spl6_39 | spl6_32),
% 0.22/0.55    inference(avatar_split_clause,[],[f288,f267,f297])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    spl6_32 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.55  fof(f288,plain,(
% 0.22/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | spl6_32),
% 0.22/0.55    inference(resolution,[],[f268,f83])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | spl6_32),
% 0.22/0.55    inference(avatar_component_clause,[],[f267])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    ~spl6_4 | spl6_31),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f284])).
% 0.22/0.55  fof(f284,plain,(
% 0.22/0.55    $false | (~spl6_4 | spl6_31)),
% 0.22/0.55    inference(subsumption_resolution,[],[f108,f283])).
% 0.22/0.55  fof(f283,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_31),
% 0.22/0.55    inference(resolution,[],[f265,f85])).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    ~v1_relat_1(sK5) | spl6_31),
% 0.22/0.55    inference(avatar_component_clause,[],[f264])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    ~spl6_27 | spl6_23 | spl6_28 | ~spl6_4 | spl6_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f219,f147,f107,f246,f229,f243])).
% 0.22/0.55  fof(f229,plain,(
% 0.22/0.55    spl6_23 <=> v1_xboole_0(k1_relat_1(sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK2)) | v1_xboole_0(k1_relat_1(sK5)) | k1_xboole_0 != k3_xboole_0(sK2,k1_relat_1(sK5)) | (~spl6_4 | spl6_14)),
% 0.22/0.55    inference(superposition,[],[f204,f208])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(k1_relat_1(sK5),X0)) ) | ~spl6_4),
% 0.22/0.55    inference(resolution,[],[f166,f108])).
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,sK2) | v1_xboole_0(X2) | k1_xboole_0 != k3_xboole_0(sK2,X2)) ) | spl6_14),
% 0.22/0.55    inference(resolution,[],[f200,f148])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ~v1_xboole_0(sK2) | spl6_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f147])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    ( ! [X2,X3] : (v1_xboole_0(X3) | k1_xboole_0 = k3_xboole_0(X2,X3) | v1_xboole_0(X2) | k1_xboole_0 != k3_xboole_0(X3,X2)) )),
% 0.22/0.55    inference(resolution,[],[f194,f83])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k3_xboole_0(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f191])).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | k3_xboole_0(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.22/0.55    inference(resolution,[],[f177,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    ( ! [X2,X3] : (~r1_subset_1(X2,X3) | v1_xboole_0(X3) | k1_xboole_0 = k3_xboole_0(X3,X2) | v1_xboole_0(X2)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f176])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    ( ! [X2,X3] : (v1_xboole_0(X2) | v1_xboole_0(X3) | k1_xboole_0 = k3_xboole_0(X3,X2) | ~r1_subset_1(X2,X3) | v1_xboole_0(X3) | v1_xboole_0(X2)) )),
% 0.22/0.55    inference(resolution,[],[f165,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.55    inference(resolution,[],[f78,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f53])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    spl6_18 | spl6_14 | spl6_12 | ~spl6_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f174,f131,f139,f147,f180])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    spl6_10 <=> r1_subset_1(sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    v1_xboole_0(sK3) | v1_xboole_0(sK2) | k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_10),
% 0.22/0.55    inference(resolution,[],[f165,f132])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    r1_subset_1(sK2,sK3) | ~spl6_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f131])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ~spl6_16),
% 0.22/0.55    inference(avatar_split_clause,[],[f54,f155])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ~v1_xboole_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f47,f46,f45,f44,f43,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  % (19170)Refutation not found, incomplete strategy% (19170)------------------------------
% 0.22/0.55  % (19170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  fof(f18,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f17])).
% 0.22/0.55  fof(f17,conjecture,(
% 0.22/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ~spl6_15),
% 0.22/0.55    inference(avatar_split_clause,[],[f55,f151])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ~v1_xboole_0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ~spl6_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f56,f147])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ~v1_xboole_0(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    spl6_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f57,f143])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ~spl6_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f58,f139])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ~v1_xboole_0(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl6_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f59,f135])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    spl6_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f60,f131])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    r1_subset_1(sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    spl6_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f61,f127])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    v1_funct_1(sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    spl6_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f62,f123])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    v1_funct_2(sK4,sK2,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl6_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f63,f119])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    spl6_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f64,f115])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    v1_funct_1(sK5)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    spl6_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f65,f111])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    v1_funct_2(sK5,sK3,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    spl6_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f66,f107])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f67,f103,f100,f97])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (19176)------------------------------
% 0.22/0.55  % (19176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19176)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (19176)Memory used [KB]: 11641
% 0.22/0.55  % (19176)Time elapsed: 0.114 s
% 0.22/0.55  % (19176)------------------------------
% 0.22/0.55  % (19176)------------------------------
% 0.22/0.55  % (19170)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19170)Memory used [KB]: 7164
% 0.22/0.55  % (19169)Success in time 0.185 s
%------------------------------------------------------------------------------
