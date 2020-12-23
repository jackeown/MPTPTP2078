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
% DateTime   : Thu Dec  3 13:17:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 541 expanded)
%              Number of leaves         :   55 ( 263 expanded)
%              Depth                    :   15
%              Number of atoms          : 1145 (4785 expanded)
%              Number of equality atoms :  186 ( 948 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f170,f175,f197,f216,f233,f252,f258,f269,f274,f276,f285,f298,f314,f323,f340,f350,f648,f653,f686,f692])).

fof(f692,plain,
    ( spl7_16
    | spl7_15
    | spl7_14
    | ~ spl7_13
    | spl7_12
    | ~ spl7_11
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f691,f90,f87,f97,f101,f105,f109,f113,f117,f125,f129,f133,f137,f141,f145])).

fof(f145,plain,
    ( spl7_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f141,plain,
    ( spl7_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f137,plain,
    ( spl7_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f133,plain,
    ( spl7_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f129,plain,
    ( spl7_12
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f125,plain,
    ( spl7_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f117,plain,
    ( spl7_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f113,plain,
    ( spl7_8
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f109,plain,
    ( spl7_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f105,plain,
    ( spl7_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f101,plain,
    ( spl7_5
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f97,plain,
    ( spl7_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f87,plain,
    ( spl7_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f90,plain,
    ( spl7_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f691,plain,
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
    | ~ spl7_1
    | spl7_2 ),
    inference(trivial_inequality_removal,[],[f690])).

fof(f690,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
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
    | ~ spl7_1
    | spl7_2 ),
    inference(forward_demodulation,[],[f689,f300])).

fof(f300,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f689,plain,
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
    | spl7_2 ),
    inference(trivial_inequality_removal,[],[f687])).

fof(f687,plain,
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
    | spl7_2 ),
    inference(superposition,[],[f91,f156])).

fof(f156,plain,(
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
    inference(subsumption_resolution,[],[f154,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f154,plain,(
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
    inference(subsumption_resolution,[],[f152,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f152,plain,(
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
    inference(subsumption_resolution,[],[f85,f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f91,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f686,plain,
    ( ~ spl7_13
    | spl7_14
    | spl7_3
    | ~ spl7_7
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f684,f651,f117,f113,f87,f109,f93,f137,f133])).

fof(f93,plain,
    ( spl7_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f651,plain,
    ( spl7_48
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f684,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_48 ),
    inference(trivial_inequality_removal,[],[f683])).

fof(f683,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_48 ),
    inference(forward_demodulation,[],[f682,f300])).

fof(f682,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_48 ),
    inference(resolution,[],[f655,f114])).

fof(f114,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f655,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK4,X1,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,X1,sK3),sK1,k1_tmap_1(sK0,sK1,X1,sK3,sK4,sK5),sK3)
        | v1_xboole_0(X1)
        | k2_partfun1(X1,sK1,sK4,k9_subset_1(sK0,X1,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X1,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl7_9
    | ~ spl7_48 ),
    inference(resolution,[],[f652,f118])).

fof(f118,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f652,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f651])).

fof(f653,plain,
    ( spl7_48
    | spl7_16
    | ~ spl7_11
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f649,f646,f125,f145,f651])).

fof(f646,plain,
    ( spl7_47
  <=> ! [X1,X0,X2] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f649,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) )
    | ~ spl7_11
    | ~ spl7_47 ),
    inference(resolution,[],[f647,f126])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f647,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f646])).

fof(f648,plain,
    ( spl7_15
    | spl7_12
    | spl7_47
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f644,f105,f101,f97,f646,f129,f141])).

fof(f644,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X2) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f552,f102])).

fof(f102,plain,
    ( v1_funct_2(sK5,sK3,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f552,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK5,X4,X1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
        | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4))
        | sK5 = k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X3) )
    | ~ spl7_6 ),
    inference(resolution,[],[f157,f106])).

fof(f106,plain,
    ( v1_funct_1(sK5)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f157,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f155,f79])).

fof(f155,plain,(
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
    inference(subsumption_resolution,[],[f153,f80])).

fof(f153,plain,(
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
    inference(subsumption_resolution,[],[f84,f81])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f350,plain,
    ( spl7_29
    | spl7_27
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f349,f296,f231,f240])).

fof(f240,plain,
    ( spl7_29
  <=> ! [X1,X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f231,plain,
    ( spl7_27
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f296,plain,
    ( spl7_35
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_35 ),
    inference(forward_demodulation,[],[f345,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f345,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(sK4,k1_xboole_0) = k3_xboole_0(sK4,k1_xboole_0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_35 ),
    inference(superposition,[],[f183,f297])).

fof(f297,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f296])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f70,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f340,plain,
    ( spl7_26
    | spl7_37
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f339,f283,f305,f228])).

fof(f228,plain,
    ( spl7_26
  <=> ! [X1,X0] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f305,plain,
    ( spl7_37
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f283,plain,
    ( spl7_34
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f339,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f335,f62])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(sK5,k1_xboole_0) = k3_xboole_0(sK5,k1_xboole_0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_34 ),
    inference(superposition,[],[f183,f284])).

fof(f284,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f283])).

fof(f323,plain,
    ( ~ spl7_37
    | spl7_23
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f321,f231,f207,f305])).

fof(f207,plain,
    ( spl7_23
  <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f321,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | spl7_23
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f208,f243])).

fof(f243,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f208,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f314,plain,
    ( ~ spl7_11
    | ~ spl7_23
    | ~ spl7_19
    | spl7_24 ),
    inference(avatar_split_clause,[],[f218,f214,f173,f207,f125])).

fof(f173,plain,
    ( spl7_19
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f214,plain,
    ( spl7_24
  <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f218,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_19
    | spl7_24 ),
    inference(forward_demodulation,[],[f217,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f217,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl7_24 ),
    inference(superposition,[],[f215,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f215,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f214])).

fof(f298,plain,
    ( spl7_35
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f293,f267,f296])).

fof(f267,plain,
    ( spl7_32
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f293,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))
    | ~ spl7_32 ),
    inference(resolution,[],[f268,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f268,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f267])).

fof(f285,plain,
    ( spl7_34
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f280,f250,f283])).

fof(f250,plain,
    ( spl7_30
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f280,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))
    | ~ spl7_30 ),
    inference(resolution,[],[f251,f68])).

fof(f251,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f250])).

fof(f276,plain,
    ( ~ spl7_7
    | ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f110,f241])).

fof(f241,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f240])).

fof(f110,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f274,plain,
    ( spl7_28
    | spl7_29
    | ~ spl7_17
    | spl7_27 ),
    inference(avatar_split_clause,[],[f260,f231,f149,f240,f237])).

fof(f237,plain,
    ( spl7_28
  <=> v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f149,plain,
    ( spl7_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))) )
    | ~ spl7_17
    | spl7_27 ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))) )
    | ~ spl7_17
    | spl7_27 ),
    inference(superposition,[],[f232,f220])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) )
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f219,f62])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k1_xboole_0) = k7_relat_1(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) )
    | ~ spl7_17 ),
    inference(superposition,[],[f183,f180])).

fof(f180,plain,
    ( ! [X5] :
        ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X5)
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,X5))) )
    | ~ spl7_17 ),
    inference(resolution,[],[f163,f68])).

fof(f163,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl7_17 ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl7_17 ),
    inference(resolution,[],[f71,f150])).

fof(f150,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f232,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f269,plain,
    ( spl7_32
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f261,f237,f267])).

fof(f261,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))
    | ~ spl7_28 ),
    inference(resolution,[],[f238,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK6(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f238,plain,
    ( v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f237])).

fof(f258,plain,
    ( ~ spl7_4
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f98,f229])).

fof(f229,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f98,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f252,plain,
    ( spl7_30
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f244,f225,f250])).

fof(f225,plain,
    ( spl7_25
  <=> v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f244,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)))
    | ~ spl7_25 ),
    inference(resolution,[],[f226,f67])).

fof(f226,plain,
    ( v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f233,plain,
    ( spl7_25
    | spl7_26
    | ~ spl7_27
    | ~ spl7_17
    | spl7_23 ),
    inference(avatar_split_clause,[],[f223,f207,f149,f231,f228,f225])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)))) )
    | ~ spl7_17
    | spl7_23 ),
    inference(superposition,[],[f208,f220])).

fof(f216,plain,
    ( ~ spl7_9
    | ~ spl7_7
    | ~ spl7_24
    | spl7_21 ),
    inference(avatar_split_clause,[],[f211,f195,f214,f109,f117])).

fof(f195,plain,
    ( spl7_21
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f211,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | spl7_21 ),
    inference(superposition,[],[f196,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f196,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( ~ spl7_6
    | ~ spl7_4
    | ~ spl7_21
    | spl7_1 ),
    inference(avatar_split_clause,[],[f191,f87,f195,f97,f105])).

fof(f191,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | spl7_1 ),
    inference(superposition,[],[f88,f78])).

fof(f88,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f175,plain,
    ( spl7_19
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f171,f168,f173])).

fof(f168,plain,
    ( spl7_18
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f171,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f169,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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

fof(f169,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl7_14
    | spl7_12
    | spl7_18
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f164,f121,f168,f129,f137])).

fof(f121,plain,
    ( spl7_10
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f164,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f72,f122])).

fof(f122,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f151,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f61,f149])).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f147,plain,(
    ~ spl7_16 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f39,f38,f37,f36,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f143,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f48,f141])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f139,plain,(
    ~ spl7_14 ),
    inference(avatar_split_clause,[],[f49,f137])).

fof(f49,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f135,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f50,f133])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f131,plain,(
    ~ spl7_12 ),
    inference(avatar_split_clause,[],[f51,f129])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f127,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f52,f125])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f123,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f54,f117])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f115,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f55,f113])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f56,f109])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f107,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f59,f97])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f60,f93,f90,f87])).

fof(f60,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (10418)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.46  % (10408)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (10408)Refutation not found, incomplete strategy% (10408)------------------------------
% 0.21/0.47  % (10408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10420)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (10408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10408)Memory used [KB]: 10746
% 0.21/0.48  % (10408)Time elapsed: 0.053 s
% 0.21/0.48  % (10408)------------------------------
% 0.21/0.48  % (10408)------------------------------
% 0.21/0.48  % (10423)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (10410)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (10416)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (10419)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (10413)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (10412)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (10411)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (10421)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (10422)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (10414)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (10407)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (10409)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (10425)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (10426)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (10415)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (10427)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (10424)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (10427)Refutation not found, incomplete strategy% (10427)------------------------------
% 0.21/0.52  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10427)Memory used [KB]: 10618
% 0.21/0.52  % (10427)Time elapsed: 0.109 s
% 0.21/0.52  % (10427)------------------------------
% 0.21/0.52  % (10427)------------------------------
% 0.21/0.52  % (10417)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.54  % (10410)Refutation not found, incomplete strategy% (10410)------------------------------
% 0.21/0.54  % (10410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10410)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10410)Memory used [KB]: 11257
% 0.21/0.54  % (10410)Time elapsed: 0.121 s
% 0.21/0.54  % (10410)------------------------------
% 0.21/0.54  % (10410)------------------------------
% 0.21/0.54  % (10413)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f697,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f170,f175,f197,f216,f233,f252,f258,f269,f274,f276,f285,f298,f314,f323,f340,f350,f648,f653,f686,f692])).
% 0.21/0.54  fof(f692,plain,(
% 0.21/0.54    spl7_16 | spl7_15 | spl7_14 | ~spl7_13 | spl7_12 | ~spl7_11 | ~spl7_9 | ~spl7_8 | ~spl7_7 | ~spl7_6 | ~spl7_5 | ~spl7_4 | ~spl7_1 | spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f691,f90,f87,f97,f101,f105,f109,f113,f117,f125,f129,f133,f137,f141,f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    spl7_16 <=> v1_xboole_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl7_15 <=> v1_xboole_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    spl7_14 <=> v1_xboole_0(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl7_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl7_12 <=> v1_xboole_0(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl7_11 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl7_9 <=> v1_funct_1(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    spl7_8 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl7_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl7_6 <=> v1_funct_1(sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl7_5 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl7_4 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl7_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl7_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f691,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl7_1 | spl7_2)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f690])).
% 0.21/0.54  fof(f690,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl7_1 | spl7_2)),
% 0.21/0.54    inference(forward_demodulation,[],[f689,f300])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f689,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl7_2),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f687])).
% 0.21/0.54  fof(f687,plain,(
% 0.21/0.54    sK4 != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl7_2),
% 0.21/0.54    inference(superposition,[],[f91,f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f152,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f90])).
% 0.21/0.54  fof(f686,plain,(
% 0.21/0.54    ~spl7_13 | spl7_14 | spl7_3 | ~spl7_7 | ~spl7_1 | ~spl7_8 | ~spl7_9 | ~spl7_48),
% 0.21/0.54    inference(avatar_split_clause,[],[f684,f651,f117,f113,f87,f109,f93,f137,f133])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl7_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f651,plain,(
% 0.21/0.54    spl7_48 <=> ! [X1,X0] : (v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.21/0.54  fof(f684,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl7_1 | ~spl7_8 | ~spl7_9 | ~spl7_48)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f683])).
% 0.21/0.54  fof(f683,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl7_1 | ~spl7_8 | ~spl7_9 | ~spl7_48)),
% 0.21/0.54    inference(forward_demodulation,[],[f682,f300])).
% 0.21/0.54  fof(f682,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | v1_xboole_0(sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl7_8 | ~spl7_9 | ~spl7_48)),
% 0.21/0.54    inference(resolution,[],[f655,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    v1_funct_2(sK4,sK2,sK1) | ~spl7_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f113])).
% 0.21/0.54  fof(f655,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_2(sK4,X1,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,X1,sK3),sK1,k1_tmap_1(sK0,sK1,X1,sK3,sK4,sK5),sK3) | v1_xboole_0(X1) | k2_partfun1(X1,sK1,sK4,k9_subset_1(sK0,X1,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X1,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | (~spl7_9 | ~spl7_48)),
% 0.21/0.54    inference(resolution,[],[f652,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    v1_funct_1(sK4) | ~spl7_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f117])).
% 0.21/0.54  fof(f652,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl7_48),
% 0.21/0.54    inference(avatar_component_clause,[],[f651])).
% 0.21/0.54  fof(f653,plain,(
% 0.21/0.54    spl7_48 | spl7_16 | ~spl7_11 | ~spl7_47),
% 0.21/0.54    inference(avatar_split_clause,[],[f649,f646,f125,f145,f651])).
% 0.21/0.54  fof(f646,plain,(
% 0.21/0.54    spl7_47 <=> ! [X1,X0,X2] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.21/0.54  fof(f649,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)) ) | (~spl7_11 | ~spl7_47)),
% 0.21/0.54    inference(resolution,[],[f647,f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f125])).
% 0.21/0.54  fof(f647,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)) ) | ~spl7_47),
% 0.21/0.54    inference(avatar_component_clause,[],[f646])).
% 0.21/0.54  fof(f648,plain,(
% 0.21/0.54    spl7_15 | spl7_12 | spl7_47 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f644,f105,f101,f97,f646,f129,f141])).
% 0.21/0.54  fof(f644,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(X2)) ) | (~spl7_5 | ~spl7_6)),
% 0.21/0.54    inference(resolution,[],[f552,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,sK1) | ~spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f552,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK5,X4,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4)) | sK5 = k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X3)) ) | ~spl7_6),
% 0.21/0.54    inference(resolution,[],[f157,f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    v1_funct_1(sK5) | ~spl7_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f155,f79])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f153,f80])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f84,f81])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f350,plain,(
% 0.21/0.54    spl7_29 | spl7_27 | ~spl7_35),
% 0.21/0.54    inference(avatar_split_clause,[],[f349,f296,f231,f240])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    spl7_29 <=> ! [X1,X0] : ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    spl7_27 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    spl7_35 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_35),
% 0.21/0.54    inference(forward_demodulation,[],[f345,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.54  fof(f345,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(sK4,k1_xboole_0) = k3_xboole_0(sK4,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_35),
% 0.21/0.54    inference(superposition,[],[f183,f297])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)) | ~spl7_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f296])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k7_relat_1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.54    inference(resolution,[],[f70,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    spl7_26 | spl7_37 | ~spl7_34),
% 0.21/0.54    inference(avatar_split_clause,[],[f339,f283,f305,f228])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    spl7_26 <=> ! [X1,X0] : ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    spl7_37 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    spl7_34 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_34),
% 0.21/0.54    inference(forward_demodulation,[],[f335,f62])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(sK5,k1_xboole_0) = k3_xboole_0(sK5,k1_xboole_0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_34),
% 0.21/0.54    inference(superposition,[],[f183,f284])).
% 0.21/0.54  fof(f284,plain,(
% 0.21/0.54    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)) | ~spl7_34),
% 0.21/0.54    inference(avatar_component_clause,[],[f283])).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    ~spl7_37 | spl7_23 | ~spl7_27),
% 0.21/0.54    inference(avatar_split_clause,[],[f321,f231,f207,f305])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    spl7_23 <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (spl7_23 | ~spl7_27)),
% 0.21/0.54    inference(forward_demodulation,[],[f208,f243])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_27),
% 0.21/0.54    inference(avatar_component_clause,[],[f231])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl7_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f207])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    ~spl7_11 | ~spl7_23 | ~spl7_19 | spl7_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f218,f214,f173,f207,f125])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl7_19 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    spl7_24 <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl7_19 | spl7_24)),
% 0.21/0.54    inference(forward_demodulation,[],[f217,f174])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl7_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f173])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl7_24),
% 0.21/0.54    inference(superposition,[],[f215,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | spl7_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f214])).
% 0.21/0.54  fof(f298,plain,(
% 0.21/0.54    spl7_35 | ~spl7_32),
% 0.21/0.54    inference(avatar_split_clause,[],[f293,f267,f296])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    spl7_32 <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)) | ~spl7_32),
% 0.21/0.54    inference(resolution,[],[f268,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) | ~spl7_32),
% 0.21/0.54    inference(avatar_component_clause,[],[f267])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    spl7_34 | ~spl7_30),
% 0.21/0.54    inference(avatar_split_clause,[],[f280,f250,f283])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    spl7_30 <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)) | ~spl7_30),
% 0.21/0.54    inference(resolution,[],[f251,f68])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))) | ~spl7_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f250])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    ~spl7_7 | ~spl7_29),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    $false | (~spl7_7 | ~spl7_29)),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f241])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f240])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f109])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    spl7_28 | spl7_29 | ~spl7_17 | spl7_27),
% 0.21/0.54    inference(avatar_split_clause,[],[f260,f231,f149,f240,f237])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    spl7_28 <=> v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    spl7_17 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.54  fof(f260,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))) ) | (~spl7_17 | spl7_27)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f259])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))))) ) | (~spl7_17 | spl7_27)),
% 0.21/0.54    inference(superposition,[],[f232,f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))) ) | ~spl7_17),
% 0.21/0.54    inference(forward_demodulation,[],[f219,f62])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k1_xboole_0) = k7_relat_1(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))) ) | ~spl7_17),
% 0.21/0.54    inference(superposition,[],[f183,f180])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X5) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,X5)))) ) | ~spl7_17),
% 0.21/0.54    inference(resolution,[],[f163,f68])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl7_17),
% 0.21/0.54    inference(resolution,[],[f162,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0] : ((~v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl7_17),
% 0.21/0.54    inference(resolution,[],[f71,f150])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0) | ~spl7_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f149])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl7_27),
% 0.21/0.54    inference(avatar_component_clause,[],[f231])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    spl7_32 | ~spl7_28),
% 0.21/0.54    inference(avatar_split_clause,[],[f261,f237,f267])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) | ~spl7_28),
% 0.21/0.54    inference(resolution,[],[f238,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(sK6(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4)))) | ~spl7_28),
% 0.21/0.54    inference(avatar_component_clause,[],[f237])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ~spl7_4 | ~spl7_26),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    $false | (~spl7_4 | ~spl7_26)),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f229])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f228])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    spl7_30 | ~spl7_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f244,f225,f250])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    spl7_25 <=> v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))) | ~spl7_25),
% 0.21/0.54    inference(resolution,[],[f226,f67])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5)))) | ~spl7_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f225])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    spl7_25 | spl7_26 | ~spl7_27 | ~spl7_17 | spl7_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f223,f207,f149,f231,f228,f225])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(sK6(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK5))))) ) | (~spl7_17 | spl7_23)),
% 0.21/0.54    inference(superposition,[],[f208,f220])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ~spl7_9 | ~spl7_7 | ~spl7_24 | spl7_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f211,f195,f214,f109,f117])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    spl7_21 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | spl7_21),
% 0.21/0.54    inference(superposition,[],[f196,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f195])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ~spl7_6 | ~spl7_4 | ~spl7_21 | spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f191,f87,f195,f97,f105])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | spl7_1),
% 0.21/0.54    inference(superposition,[],[f88,f78])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    spl7_19 | ~spl7_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f171,f168,f173])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    spl7_18 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl7_18),
% 0.21/0.54    inference(resolution,[],[f169,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK3) | ~spl7_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f168])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    spl7_14 | spl7_12 | spl7_18 | ~spl7_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f164,f121,f168,f129,f137])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl7_10 <=> r1_subset_1(sK2,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) | ~spl7_10),
% 0.21/0.54    inference(resolution,[],[f72,f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    r1_subset_1(sK2,sK3) | ~spl7_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f121])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    spl7_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f61,f149])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ~spl7_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f145])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f39,f38,f37,f36,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f15])).
% 0.21/0.54  fof(f15,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ~spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f141])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ~spl7_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f137])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ~v1_xboole_0(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl7_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f133])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ~spl7_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f129])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ~v1_xboole_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl7_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f125])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl7_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f53,f121])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    r1_subset_1(sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl7_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f117])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    spl7_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f55,f113])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f56,f109])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f57,f105])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f58,f101])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f59,f97])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f60,f93,f90,f87])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (10413)------------------------------
% 0.21/0.54  % (10413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10413)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (10413)Memory used [KB]: 11385
% 0.21/0.54  % (10413)Time elapsed: 0.076 s
% 0.21/0.54  % (10413)------------------------------
% 0.21/0.54  % (10413)------------------------------
% 0.21/0.55  % (10406)Success in time 0.186 s
%------------------------------------------------------------------------------
