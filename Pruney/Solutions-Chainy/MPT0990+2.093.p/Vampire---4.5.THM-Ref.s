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
% DateTime   : Thu Dec  3 13:02:44 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 552 expanded)
%              Number of leaves         :   46 ( 229 expanded)
%              Depth                    :   16
%              Number of atoms          : 1210 (2870 expanded)
%              Number of equality atoms :  233 ( 731 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f572,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f152,f161,f166,f196,f208,f225,f239,f257,f269,f287,f333,f380,f402,f413,f455,f486,f569])).

fof(f569,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34
    | ~ spl4_37
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34
    | ~ spl4_37
    | spl4_40 ),
    inference(subsumption_resolution,[],[f567,f454])).

fof(f454,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl4_40
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f567,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f566,f80])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f566,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f565,f160])).

fof(f160,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f565,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f564,f130])).

fof(f130,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f564,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f553,f358])).

fof(f358,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl4_34
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f553,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f63,f379])).

fof(f379,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl4_37
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
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
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f486,plain,
    ( spl4_34
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f485,f193,f143,f138,f133,f128,f123,f118,f113,f98,f356])).

fof(f98,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f113,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f118,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f123,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f133,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f138,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f143,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f193,plain,
    ( spl4_19
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f485,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f484,f130])).

fof(f484,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f483,f125])).

fof(f125,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f483,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f482,f120])).

fof(f120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f482,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f471,f100])).

fof(f100,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f471,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f463,f71])).

fof(f71,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f463,plain,
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
    | ~ spl4_19 ),
    inference(superposition,[],[f340,f195])).

fof(f195,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f340,plain,
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
    inference(subsumption_resolution,[],[f339,f145])).

fof(f145,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f339,plain,
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
    inference(subsumption_resolution,[],[f338,f140])).

fof(f140,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f338,plain,
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
    inference(subsumption_resolution,[],[f337,f135])).

fof(f135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f337,plain,
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
    inference(trivial_inequality_removal,[],[f336])).

fof(f336,plain,
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
    inference(superposition,[],[f67,f115])).

fof(f115,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f455,plain,
    ( ~ spl4_40
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f450,f279,f249,f222,f163,f158,f143,f128,f88,f452])).

fof(f88,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f163,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f222,plain,
    ( spl4_22
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f249,plain,
    ( spl4_24
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f279,plain,
    ( spl4_26
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f450,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f449,f281])).

fof(f281,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f279])).

fof(f449,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(trivial_inequality_removal,[],[f448])).

fof(f448,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f447,f251])).

fof(f251,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f447,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f446,f165])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f446,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f445,f145])).

fof(f445,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f444,f160])).

fof(f444,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f443,f130])).

fof(f443,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f437,f90])).

fof(f90,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f437,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f184,f224])).

fof(f224,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f184,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f60,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
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
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
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
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
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
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f413,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f145,f130,f135,f120,f220,f215])).

fof(f215,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
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
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f220,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_21
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f402,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_18 ),
    inference(subsumption_resolution,[],[f400,f145])).

fof(f400,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_18 ),
    inference(subsumption_resolution,[],[f399,f135])).

fof(f399,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_18 ),
    inference(subsumption_resolution,[],[f398,f130])).

fof(f398,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_18 ),
    inference(subsumption_resolution,[],[f395,f120])).

fof(f395,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_18 ),
    inference(resolution,[],[f191,f78])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_18
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f380,plain,
    ( spl4_37
    | ~ spl4_34
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f375,f330,f128,f123,f118,f98,f356,f377])).

fof(f330,plain,
    ( spl4_33
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f375,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f374,f130])).

fof(f374,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f373,f125])).

fof(f373,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f372,f120])).

fof(f372,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f345,f100])).

fof(f345,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_33 ),
    inference(trivial_inequality_removal,[],[f344])).

fof(f344,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_33 ),
    inference(superposition,[],[f226,f332])).

fof(f332,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f330])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f58,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f333,plain,
    ( spl4_33
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f328,f149,f143,f138,f133,f128,f123,f118,f330])).

fof(f149,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f328,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f327,f130])).

fof(f327,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f326,f125])).

fof(f326,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f325,f120])).

fof(f325,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f324,f145])).

fof(f324,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f323,f140])).

fof(f323,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f320,f135])).

fof(f320,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f319,f151])).

fof(f151,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f319,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f74,f76])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f287,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f286,f266,f163,f143,f103,f279])).

fof(f103,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f266,plain,
    ( spl4_25
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f286,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f285,f80])).

fof(f285,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f284,f165])).

fof(f284,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f283,f145])).

fof(f283,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f271,f105])).

fof(f105,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f271,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_25 ),
    inference(superposition,[],[f61,f268])).

fof(f268,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f266])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f269,plain,
    ( spl4_25
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f264,f143,f138,f133,f113,f103,f93,f266])).

fof(f93,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f264,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f263,f145])).

fof(f263,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f262,f140])).

fof(f262,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f261,f135])).

fof(f261,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f260,f105])).

fof(f260,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f259,f95])).

fof(f95,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f227,f115])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f59,f76])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f257,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f256,f236,f163,f143,f103,f249])).

fof(f236,plain,
    ( spl4_23
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f256,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f255,f80])).

fof(f255,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f254,f165])).

fof(f254,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f253,f145])).

fof(f253,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f241,f105])).

fof(f241,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f63,f238])).

fof(f238,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f236])).

fof(f239,plain,
    ( spl4_23
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f234,f143,f138,f133,f113,f103,f93,f236])).

fof(f234,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f233,f145])).

fof(f233,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f232,f140])).

fof(f232,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f231,f135])).

fof(f231,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f230,f105])).

fof(f230,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f229,f95])).

fof(f229,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f226,f115])).

fof(f225,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f216,f205,f222,f218])).

fof(f205,plain,
    ( spl4_20
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f216,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_20 ),
    inference(resolution,[],[f207,f182])).

fof(f182,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f72,f153])).

fof(f153,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f207,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f208,plain,
    ( spl4_20
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f203,f149,f143,f133,f128,f118,f205])).

fof(f203,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f202,f145])).

fof(f202,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f201,f135])).

fof(f201,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f200,f130])).

fof(f200,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f197,f120])).

fof(f197,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f151,f79])).

fof(f196,plain,
    ( ~ spl4_18
    | spl4_19
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f186,f149,f193,f189])).

fof(f186,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f182,f151])).

fof(f166,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f155,f133,f163])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f82,f135])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f161,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f154,f118,f158])).

fof(f154,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f82,f120])).

fof(f152,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f147,f108,f149])).

fof(f108,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f147,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f110,f76])).

fof(f110,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f146,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f46,f143])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f141,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f47,f138])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f136,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f48,f133])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f131,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f49,f128])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f50,f123])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f51,f118])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f55,f98])).

fof(f55,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f93])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f57,f88])).

fof(f57,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (22604)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (22596)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (22589)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (22581)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (22590)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (22580)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (22600)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (22582)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (22579)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (22603)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (22605)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (22597)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (22584)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (22586)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (22607)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (22578)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (22606)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (22601)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (22595)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (22602)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (22599)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (22591)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (22598)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (22593)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (22587)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (22592)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (22583)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.55  % (22594)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (22594)Refutation not found, incomplete strategy% (22594)------------------------------
% 0.20/0.55  % (22594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22594)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22594)Memory used [KB]: 10746
% 0.20/0.55  % (22594)Time elapsed: 0.150 s
% 0.20/0.55  % (22594)------------------------------
% 0.20/0.55  % (22594)------------------------------
% 0.20/0.55  % (22588)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (22585)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (22588)Refutation not found, incomplete strategy% (22588)------------------------------
% 0.20/0.56  % (22588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22588)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22588)Memory used [KB]: 11001
% 0.20/0.56  % (22588)Time elapsed: 0.152 s
% 0.20/0.56  % (22588)------------------------------
% 0.20/0.56  % (22588)------------------------------
% 1.56/0.57  % (22606)Refutation not found, incomplete strategy% (22606)------------------------------
% 1.56/0.57  % (22606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (22606)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (22606)Memory used [KB]: 11001
% 1.56/0.57  % (22606)Time elapsed: 0.141 s
% 1.56/0.57  % (22606)------------------------------
% 1.56/0.57  % (22606)------------------------------
% 1.71/0.58  % (22599)Refutation found. Thanks to Tanya!
% 1.71/0.58  % SZS status Theorem for theBenchmark
% 1.71/0.58  % SZS output start Proof for theBenchmark
% 1.71/0.58  fof(f572,plain,(
% 1.71/0.58    $false),
% 1.71/0.58    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f152,f161,f166,f196,f208,f225,f239,f257,f269,f287,f333,f380,f402,f413,f455,f486,f569])).
% 1.71/0.58  fof(f569,plain,(
% 1.71/0.58    ~spl4_9 | ~spl4_14 | ~spl4_34 | ~spl4_37 | spl4_40),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f568])).
% 1.71/0.58  fof(f568,plain,(
% 1.71/0.58    $false | (~spl4_9 | ~spl4_14 | ~spl4_34 | ~spl4_37 | spl4_40)),
% 1.71/0.58    inference(subsumption_resolution,[],[f567,f454])).
% 1.71/0.58  fof(f454,plain,(
% 1.71/0.58    sK1 != k1_relat_1(sK3) | spl4_40),
% 1.71/0.58    inference(avatar_component_clause,[],[f452])).
% 1.71/0.58  fof(f452,plain,(
% 1.71/0.58    spl4_40 <=> sK1 = k1_relat_1(sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.71/0.58  fof(f567,plain,(
% 1.71/0.58    sK1 = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_34 | ~spl4_37)),
% 1.71/0.58    inference(forward_demodulation,[],[f566,f80])).
% 1.71/0.58  fof(f80,plain,(
% 1.71/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f1])).
% 1.71/0.58  fof(f1,axiom,(
% 1.71/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.71/0.58  fof(f566,plain,(
% 1.71/0.58    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_34 | ~spl4_37)),
% 1.71/0.58    inference(subsumption_resolution,[],[f565,f160])).
% 1.71/0.58  fof(f160,plain,(
% 1.71/0.58    v1_relat_1(sK3) | ~spl4_14),
% 1.71/0.58    inference(avatar_component_clause,[],[f158])).
% 1.71/0.58  fof(f158,plain,(
% 1.71/0.58    spl4_14 <=> v1_relat_1(sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.71/0.58  fof(f565,plain,(
% 1.71/0.58    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_34 | ~spl4_37)),
% 1.71/0.58    inference(subsumption_resolution,[],[f564,f130])).
% 1.71/0.58  fof(f130,plain,(
% 1.71/0.58    v1_funct_1(sK3) | ~spl4_9),
% 1.71/0.58    inference(avatar_component_clause,[],[f128])).
% 1.71/0.58  fof(f128,plain,(
% 1.71/0.58    spl4_9 <=> v1_funct_1(sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.71/0.58  fof(f564,plain,(
% 1.71/0.58    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_34 | ~spl4_37)),
% 1.71/0.58    inference(subsumption_resolution,[],[f553,f358])).
% 1.71/0.58  fof(f358,plain,(
% 1.71/0.58    v2_funct_1(sK3) | ~spl4_34),
% 1.71/0.58    inference(avatar_component_clause,[],[f356])).
% 1.71/0.58  fof(f356,plain,(
% 1.71/0.58    spl4_34 <=> v2_funct_1(sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.71/0.58  fof(f553,plain,(
% 1.71/0.58    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_37),
% 1.71/0.58    inference(superposition,[],[f63,f379])).
% 1.71/0.58  fof(f379,plain,(
% 1.71/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_37),
% 1.71/0.58    inference(avatar_component_clause,[],[f377])).
% 1.71/0.58  fof(f377,plain,(
% 1.71/0.58    spl4_37 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.71/0.58  fof(f63,plain,(
% 1.71/0.58    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f28])).
% 1.71/0.58  fof(f28,plain,(
% 1.71/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.58    inference(flattening,[],[f27])).
% 1.71/0.58  fof(f27,plain,(
% 1.71/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f4])).
% 1.71/0.58  fof(f4,axiom,(
% 1.71/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.71/0.58  fof(f486,plain,(
% 1.71/0.58    spl4_34 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19),
% 1.71/0.58    inference(avatar_split_clause,[],[f485,f193,f143,f138,f133,f128,f123,f118,f113,f98,f356])).
% 1.71/0.58  fof(f98,plain,(
% 1.71/0.58    spl4_3 <=> k1_xboole_0 = sK0),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.58  fof(f113,plain,(
% 1.71/0.58    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.58  fof(f118,plain,(
% 1.71/0.58    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.58  fof(f123,plain,(
% 1.71/0.58    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.71/0.58  fof(f133,plain,(
% 1.71/0.58    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.71/0.58  fof(f138,plain,(
% 1.71/0.58    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.71/0.58  fof(f143,plain,(
% 1.71/0.58    spl4_12 <=> v1_funct_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.71/0.58  fof(f193,plain,(
% 1.71/0.58    spl4_19 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.71/0.58  fof(f485,plain,(
% 1.71/0.58    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19)),
% 1.71/0.58    inference(subsumption_resolution,[],[f484,f130])).
% 1.71/0.58  fof(f484,plain,(
% 1.71/0.58    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19)),
% 1.71/0.58    inference(subsumption_resolution,[],[f483,f125])).
% 1.71/0.58  fof(f125,plain,(
% 1.71/0.58    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.71/0.58    inference(avatar_component_clause,[],[f123])).
% 1.71/0.58  fof(f483,plain,(
% 1.71/0.58    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19)),
% 1.71/0.58    inference(subsumption_resolution,[],[f482,f120])).
% 1.71/0.58  fof(f120,plain,(
% 1.71/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.71/0.58    inference(avatar_component_clause,[],[f118])).
% 1.71/0.58  fof(f482,plain,(
% 1.71/0.58    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19)),
% 1.71/0.58    inference(subsumption_resolution,[],[f471,f100])).
% 1.71/0.58  fof(f100,plain,(
% 1.71/0.58    k1_xboole_0 != sK0 | spl4_3),
% 1.71/0.58    inference(avatar_component_clause,[],[f98])).
% 1.71/0.58  fof(f471,plain,(
% 1.71/0.58    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19)),
% 1.71/0.58    inference(subsumption_resolution,[],[f463,f71])).
% 1.71/0.58  fof(f71,plain,(
% 1.71/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f2])).
% 1.71/0.58  fof(f2,axiom,(
% 1.71/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.71/0.58  fof(f463,plain,(
% 1.71/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_19)),
% 1.71/0.58    inference(superposition,[],[f340,f195])).
% 1.71/0.58  fof(f195,plain,(
% 1.71/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_19),
% 1.71/0.58    inference(avatar_component_clause,[],[f193])).
% 1.71/0.58  fof(f340,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.71/0.58    inference(subsumption_resolution,[],[f339,f145])).
% 1.71/0.58  fof(f145,plain,(
% 1.71/0.58    v1_funct_1(sK2) | ~spl4_12),
% 1.71/0.58    inference(avatar_component_clause,[],[f143])).
% 1.71/0.58  fof(f339,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.71/0.58    inference(subsumption_resolution,[],[f338,f140])).
% 1.71/0.58  fof(f140,plain,(
% 1.71/0.58    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.71/0.58    inference(avatar_component_clause,[],[f138])).
% 1.71/0.58  fof(f338,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.71/0.58    inference(subsumption_resolution,[],[f337,f135])).
% 1.71/0.58  fof(f135,plain,(
% 1.71/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.71/0.58    inference(avatar_component_clause,[],[f133])).
% 1.71/0.58  fof(f337,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f336])).
% 1.71/0.58  fof(f336,plain,(
% 1.71/0.58    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.71/0.58    inference(superposition,[],[f67,f115])).
% 1.71/0.58  fof(f115,plain,(
% 1.71/0.58    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.71/0.58    inference(avatar_component_clause,[],[f113])).
% 1.71/0.58  fof(f67,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f30])).
% 1.71/0.58  fof(f30,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.71/0.58    inference(flattening,[],[f29])).
% 1.71/0.58  fof(f29,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.71/0.58    inference(ennf_transformation,[],[f14])).
% 1.71/0.58  fof(f14,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.71/0.58  fof(f455,plain,(
% 1.71/0.58    ~spl4_40 | spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22 | ~spl4_24 | ~spl4_26),
% 1.71/0.58    inference(avatar_split_clause,[],[f450,f279,f249,f222,f163,f158,f143,f128,f88,f452])).
% 1.71/0.58  fof(f88,plain,(
% 1.71/0.58    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.58  fof(f163,plain,(
% 1.71/0.58    spl4_15 <=> v1_relat_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.71/0.58  fof(f222,plain,(
% 1.71/0.58    spl4_22 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.71/0.58  fof(f249,plain,(
% 1.71/0.58    spl4_24 <=> sK0 = k1_relat_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.71/0.58  fof(f279,plain,(
% 1.71/0.58    spl4_26 <=> sK1 = k2_relat_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.71/0.58  fof(f450,plain,(
% 1.71/0.58    sK1 != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22 | ~spl4_24 | ~spl4_26)),
% 1.71/0.58    inference(forward_demodulation,[],[f449,f281])).
% 1.71/0.58  fof(f281,plain,(
% 1.71/0.58    sK1 = k2_relat_1(sK2) | ~spl4_26),
% 1.71/0.58    inference(avatar_component_clause,[],[f279])).
% 1.71/0.58  fof(f449,plain,(
% 1.71/0.58    k2_relat_1(sK2) != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22 | ~spl4_24)),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f448])).
% 1.71/0.58  fof(f448,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(sK0) | k2_relat_1(sK2) != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22 | ~spl4_24)),
% 1.71/0.58    inference(forward_demodulation,[],[f447,f251])).
% 1.71/0.58  fof(f251,plain,(
% 1.71/0.58    sK0 = k1_relat_1(sK2) | ~spl4_24),
% 1.71/0.58    inference(avatar_component_clause,[],[f249])).
% 1.71/0.58  fof(f447,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_22)),
% 1.71/0.58    inference(subsumption_resolution,[],[f446,f165])).
% 1.71/0.58  fof(f165,plain,(
% 1.71/0.58    v1_relat_1(sK2) | ~spl4_15),
% 1.71/0.58    inference(avatar_component_clause,[],[f163])).
% 1.71/0.58  fof(f446,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_22)),
% 1.71/0.58    inference(subsumption_resolution,[],[f445,f145])).
% 1.71/0.58  fof(f445,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_22)),
% 1.71/0.58    inference(subsumption_resolution,[],[f444,f160])).
% 1.71/0.58  fof(f444,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_22)),
% 1.71/0.58    inference(subsumption_resolution,[],[f443,f130])).
% 1.71/0.58  fof(f443,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_22)),
% 1.71/0.58    inference(subsumption_resolution,[],[f437,f90])).
% 1.71/0.58  fof(f90,plain,(
% 1.71/0.58    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.71/0.58    inference(avatar_component_clause,[],[f88])).
% 1.71/0.58  fof(f437,plain,(
% 1.71/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_22),
% 1.71/0.58    inference(superposition,[],[f184,f224])).
% 1.71/0.58  fof(f224,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_22),
% 1.71/0.58    inference(avatar_component_clause,[],[f222])).
% 1.71/0.58  fof(f184,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.58    inference(subsumption_resolution,[],[f60,f69])).
% 1.71/0.58  fof(f69,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f32])).
% 1.71/0.58  fof(f32,plain,(
% 1.71/0.58    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.58    inference(flattening,[],[f31])).
% 1.71/0.58  fof(f31,plain,(
% 1.71/0.58    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f3])).
% 1.71/0.58  fof(f3,axiom,(
% 1.71/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 1.71/0.58  fof(f60,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f24])).
% 1.71/0.58  fof(f24,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.58    inference(flattening,[],[f23])).
% 1.71/0.58  fof(f23,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f6])).
% 1.71/0.58  fof(f6,axiom,(
% 1.71/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.71/0.58  fof(f413,plain,(
% 1.71/0.58    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_21),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f403])).
% 1.71/0.58  fof(f403,plain,(
% 1.71/0.58    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_21)),
% 1.71/0.58    inference(unit_resulting_resolution,[],[f145,f130,f135,f120,f220,f215])).
% 1.71/0.58  fof(f215,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.58    inference(duplicate_literal_removal,[],[f214])).
% 1.71/0.58  fof(f214,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.58    inference(superposition,[],[f78,f79])).
% 1.71/0.58  fof(f79,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f40])).
% 1.71/0.58  fof(f40,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.58    inference(flattening,[],[f39])).
% 1.71/0.58  fof(f39,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.58    inference(ennf_transformation,[],[f11])).
% 1.71/0.58  fof(f11,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.71/0.58  fof(f78,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f38])).
% 1.71/0.58  fof(f38,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.58    inference(flattening,[],[f37])).
% 1.71/0.58  fof(f37,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.58    inference(ennf_transformation,[],[f9])).
% 1.71/0.58  fof(f9,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.71/0.58  fof(f220,plain,(
% 1.71/0.58    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_21),
% 1.71/0.58    inference(avatar_component_clause,[],[f218])).
% 1.71/0.58  fof(f218,plain,(
% 1.71/0.58    spl4_21 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.71/0.58  fof(f402,plain,(
% 1.71/0.58    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_18),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f401])).
% 1.71/0.58  fof(f401,plain,(
% 1.71/0.58    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_18)),
% 1.71/0.58    inference(subsumption_resolution,[],[f400,f145])).
% 1.71/0.58  fof(f400,plain,(
% 1.71/0.58    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_18)),
% 1.71/0.58    inference(subsumption_resolution,[],[f399,f135])).
% 1.71/0.58  fof(f399,plain,(
% 1.71/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_18)),
% 1.71/0.58    inference(subsumption_resolution,[],[f398,f130])).
% 1.71/0.58  fof(f398,plain,(
% 1.71/0.58    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_18)),
% 1.71/0.58    inference(subsumption_resolution,[],[f395,f120])).
% 1.71/0.58  fof(f395,plain,(
% 1.71/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_18),
% 1.71/0.58    inference(resolution,[],[f191,f78])).
% 1.71/0.58  fof(f191,plain,(
% 1.71/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_18),
% 1.71/0.58    inference(avatar_component_clause,[],[f189])).
% 1.71/0.58  fof(f189,plain,(
% 1.71/0.58    spl4_18 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.71/0.58  fof(f380,plain,(
% 1.71/0.58    spl4_37 | ~spl4_34 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_33),
% 1.71/0.58    inference(avatar_split_clause,[],[f375,f330,f128,f123,f118,f98,f356,f377])).
% 1.71/0.58  fof(f330,plain,(
% 1.71/0.58    spl4_33 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.71/0.58  fof(f375,plain,(
% 1.71/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_33)),
% 1.71/0.58    inference(subsumption_resolution,[],[f374,f130])).
% 1.71/0.58  fof(f374,plain,(
% 1.71/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_33)),
% 1.71/0.58    inference(subsumption_resolution,[],[f373,f125])).
% 1.71/0.58  fof(f373,plain,(
% 1.71/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_33)),
% 1.71/0.58    inference(subsumption_resolution,[],[f372,f120])).
% 1.71/0.58  fof(f372,plain,(
% 1.71/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_33)),
% 1.71/0.58    inference(subsumption_resolution,[],[f345,f100])).
% 1.71/0.58  fof(f345,plain,(
% 1.71/0.58    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_33),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f344])).
% 1.71/0.58  fof(f344,plain,(
% 1.71/0.58    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_33),
% 1.71/0.58    inference(superposition,[],[f226,f332])).
% 1.71/0.58  fof(f332,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_33),
% 1.71/0.58    inference(avatar_component_clause,[],[f330])).
% 1.71/0.58  fof(f226,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f58,f76])).
% 1.71/0.58  fof(f76,plain,(
% 1.71/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f12])).
% 1.71/0.58  fof(f12,axiom,(
% 1.71/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.71/0.58  fof(f58,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f22])).
% 1.71/0.58  fof(f22,plain,(
% 1.71/0.58    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.58    inference(flattening,[],[f21])).
% 1.71/0.58  fof(f21,plain,(
% 1.71/0.58    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.58    inference(ennf_transformation,[],[f15])).
% 1.71/0.58  fof(f15,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.71/0.58  fof(f333,plain,(
% 1.71/0.58    spl4_33 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.71/0.58    inference(avatar_split_clause,[],[f328,f149,f143,f138,f133,f128,f123,f118,f330])).
% 1.71/0.58  fof(f149,plain,(
% 1.71/0.58    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.71/0.58  fof(f328,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f327,f130])).
% 1.71/0.58  fof(f327,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f326,f125])).
% 1.71/0.58  fof(f326,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f325,f120])).
% 1.71/0.58  fof(f325,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f324,f145])).
% 1.71/0.58  fof(f324,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f323,f140])).
% 1.71/0.58  fof(f323,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f320,f135])).
% 1.71/0.58  fof(f320,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.71/0.58    inference(resolution,[],[f319,f151])).
% 1.71/0.58  fof(f151,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.71/0.58    inference(avatar_component_clause,[],[f149])).
% 1.71/0.58  fof(f319,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f74,f76])).
% 1.71/0.58  fof(f74,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f36])).
% 1.71/0.58  fof(f36,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.58    inference(flattening,[],[f35])).
% 1.71/0.58  fof(f35,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.58    inference(ennf_transformation,[],[f13])).
% 1.71/0.58  fof(f13,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.71/0.58  fof(f287,plain,(
% 1.71/0.58    spl4_26 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_25),
% 1.71/0.58    inference(avatar_split_clause,[],[f286,f266,f163,f143,f103,f279])).
% 1.71/0.58  fof(f103,plain,(
% 1.71/0.58    spl4_4 <=> v2_funct_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.58  fof(f266,plain,(
% 1.71/0.58    spl4_25 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.71/0.58  fof(f286,plain,(
% 1.71/0.58    sK1 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_25)),
% 1.71/0.58    inference(forward_demodulation,[],[f285,f80])).
% 1.71/0.58  fof(f285,plain,(
% 1.71/0.58    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_25)),
% 1.71/0.58    inference(subsumption_resolution,[],[f284,f165])).
% 1.71/0.58  fof(f284,plain,(
% 1.71/0.58    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_25)),
% 1.71/0.58    inference(subsumption_resolution,[],[f283,f145])).
% 1.71/0.58  fof(f283,plain,(
% 1.71/0.58    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_25)),
% 1.71/0.58    inference(subsumption_resolution,[],[f271,f105])).
% 1.71/0.58  fof(f105,plain,(
% 1.71/0.58    v2_funct_1(sK2) | ~spl4_4),
% 1.71/0.58    inference(avatar_component_clause,[],[f103])).
% 1.71/0.58  fof(f271,plain,(
% 1.71/0.58    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_25),
% 1.71/0.58    inference(superposition,[],[f61,f268])).
% 1.71/0.58  fof(f268,plain,(
% 1.71/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_25),
% 1.71/0.58    inference(avatar_component_clause,[],[f266])).
% 1.71/0.58  fof(f61,plain,(
% 1.71/0.58    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f26])).
% 1.71/0.58  fof(f26,plain,(
% 1.71/0.58    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.58    inference(flattening,[],[f25])).
% 1.71/0.58  fof(f25,plain,(
% 1.71/0.58    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f5])).
% 1.71/0.58  fof(f5,axiom,(
% 1.71/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.71/0.58  fof(f269,plain,(
% 1.71/0.58    spl4_25 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.71/0.58    inference(avatar_split_clause,[],[f264,f143,f138,f133,f113,f103,f93,f266])).
% 1.71/0.58  fof(f93,plain,(
% 1.71/0.58    spl4_2 <=> k1_xboole_0 = sK1),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.58  fof(f264,plain,(
% 1.71/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.71/0.58    inference(subsumption_resolution,[],[f263,f145])).
% 1.71/0.58  fof(f263,plain,(
% 1.71/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.71/0.58    inference(subsumption_resolution,[],[f262,f140])).
% 1.71/0.58  fof(f262,plain,(
% 1.71/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.71/0.58    inference(subsumption_resolution,[],[f261,f135])).
% 1.71/0.58  fof(f261,plain,(
% 1.71/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.71/0.58    inference(subsumption_resolution,[],[f260,f105])).
% 1.71/0.58  fof(f260,plain,(
% 1.71/0.58    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.71/0.58    inference(subsumption_resolution,[],[f259,f95])).
% 1.71/0.58  fof(f95,plain,(
% 1.71/0.58    k1_xboole_0 != sK1 | spl4_2),
% 1.71/0.58    inference(avatar_component_clause,[],[f93])).
% 1.71/0.58  fof(f259,plain,(
% 1.71/0.58    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f258])).
% 1.71/0.58  fof(f258,plain,(
% 1.71/0.58    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.71/0.58    inference(superposition,[],[f227,f115])).
% 1.71/0.58  fof(f227,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f59,f76])).
% 1.71/0.58  fof(f59,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f22])).
% 1.71/0.58  fof(f257,plain,(
% 1.71/0.58    spl4_24 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_23),
% 1.71/0.58    inference(avatar_split_clause,[],[f256,f236,f163,f143,f103,f249])).
% 1.71/0.58  fof(f236,plain,(
% 1.71/0.58    spl4_23 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.71/0.58  fof(f256,plain,(
% 1.71/0.58    sK0 = k1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_23)),
% 1.71/0.58    inference(forward_demodulation,[],[f255,f80])).
% 1.71/0.58  fof(f255,plain,(
% 1.71/0.58    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_23)),
% 1.71/0.58    inference(subsumption_resolution,[],[f254,f165])).
% 1.71/0.58  fof(f254,plain,(
% 1.71/0.58    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_23)),
% 1.71/0.58    inference(subsumption_resolution,[],[f253,f145])).
% 1.71/0.58  fof(f253,plain,(
% 1.71/0.58    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_23)),
% 1.71/0.58    inference(subsumption_resolution,[],[f241,f105])).
% 1.71/0.58  fof(f241,plain,(
% 1.71/0.58    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_23),
% 1.71/0.58    inference(superposition,[],[f63,f238])).
% 1.71/0.58  fof(f238,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_23),
% 1.71/0.58    inference(avatar_component_clause,[],[f236])).
% 1.71/0.58  fof(f239,plain,(
% 1.71/0.58    spl4_23 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.71/0.58    inference(avatar_split_clause,[],[f234,f143,f138,f133,f113,f103,f93,f236])).
% 1.71/0.58  fof(f234,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.71/0.58    inference(subsumption_resolution,[],[f233,f145])).
% 1.71/0.58  fof(f233,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.71/0.58    inference(subsumption_resolution,[],[f232,f140])).
% 1.71/0.58  fof(f232,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.71/0.58    inference(subsumption_resolution,[],[f231,f135])).
% 1.71/0.58  fof(f231,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.71/0.58    inference(subsumption_resolution,[],[f230,f105])).
% 1.71/0.58  fof(f230,plain,(
% 1.71/0.58    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.71/0.58    inference(subsumption_resolution,[],[f229,f95])).
% 1.71/0.58  fof(f229,plain,(
% 1.71/0.58    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f228])).
% 1.71/0.58  fof(f228,plain,(
% 1.71/0.58    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.71/0.58    inference(superposition,[],[f226,f115])).
% 1.71/0.58  fof(f225,plain,(
% 1.71/0.58    ~spl4_21 | spl4_22 | ~spl4_20),
% 1.71/0.58    inference(avatar_split_clause,[],[f216,f205,f222,f218])).
% 1.71/0.58  fof(f205,plain,(
% 1.71/0.58    spl4_20 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.71/0.58  fof(f216,plain,(
% 1.71/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_20),
% 1.71/0.58    inference(resolution,[],[f207,f182])).
% 1.71/0.58  fof(f182,plain,(
% 1.71/0.58    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.71/0.58    inference(resolution,[],[f72,f153])).
% 1.71/0.58  fof(f153,plain,(
% 1.71/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.71/0.58    inference(forward_demodulation,[],[f75,f76])).
% 1.71/0.58  fof(f75,plain,(
% 1.71/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f18])).
% 1.71/0.58  fof(f18,plain,(
% 1.71/0.58    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.71/0.58    inference(pure_predicate_removal,[],[f10])).
% 1.71/0.58  fof(f10,axiom,(
% 1.71/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.71/0.58  fof(f72,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f45])).
% 1.71/0.58  fof(f45,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(nnf_transformation,[],[f34])).
% 1.71/0.58  fof(f34,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(flattening,[],[f33])).
% 1.71/0.58  fof(f33,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.58    inference(ennf_transformation,[],[f8])).
% 1.71/0.58  fof(f8,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.71/0.58  fof(f207,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_20),
% 1.71/0.58    inference(avatar_component_clause,[],[f205])).
% 1.71/0.58  fof(f208,plain,(
% 1.71/0.58    spl4_20 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.71/0.58    inference(avatar_split_clause,[],[f203,f149,f143,f133,f128,f118,f205])).
% 1.71/0.58  fof(f203,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f202,f145])).
% 1.71/0.58  fof(f202,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f201,f135])).
% 1.71/0.58  fof(f201,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f200,f130])).
% 1.71/0.58  fof(f200,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.71/0.58    inference(subsumption_resolution,[],[f197,f120])).
% 1.71/0.58  fof(f197,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.71/0.58    inference(superposition,[],[f151,f79])).
% 1.71/0.58  fof(f196,plain,(
% 1.71/0.58    ~spl4_18 | spl4_19 | ~spl4_13),
% 1.71/0.58    inference(avatar_split_clause,[],[f186,f149,f193,f189])).
% 1.71/0.58  fof(f186,plain,(
% 1.71/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.71/0.58    inference(resolution,[],[f182,f151])).
% 1.71/0.58  fof(f166,plain,(
% 1.71/0.58    spl4_15 | ~spl4_10),
% 1.71/0.58    inference(avatar_split_clause,[],[f155,f133,f163])).
% 1.71/0.58  fof(f155,plain,(
% 1.71/0.58    v1_relat_1(sK2) | ~spl4_10),
% 1.71/0.58    inference(resolution,[],[f82,f135])).
% 1.71/0.58  fof(f82,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f41])).
% 1.71/0.58  fof(f41,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(ennf_transformation,[],[f7])).
% 1.71/0.58  fof(f7,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.71/0.58  fof(f161,plain,(
% 1.71/0.58    spl4_14 | ~spl4_7),
% 1.71/0.58    inference(avatar_split_clause,[],[f154,f118,f158])).
% 1.71/0.58  fof(f154,plain,(
% 1.71/0.58    v1_relat_1(sK3) | ~spl4_7),
% 1.71/0.58    inference(resolution,[],[f82,f120])).
% 1.71/0.58  fof(f152,plain,(
% 1.71/0.58    spl4_13 | ~spl4_5),
% 1.71/0.58    inference(avatar_split_clause,[],[f147,f108,f149])).
% 1.71/0.58  fof(f108,plain,(
% 1.71/0.58    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.71/0.58  fof(f147,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.71/0.58    inference(backward_demodulation,[],[f110,f76])).
% 1.71/0.58  fof(f110,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.71/0.58    inference(avatar_component_clause,[],[f108])).
% 1.71/0.58  fof(f146,plain,(
% 1.71/0.58    spl4_12),
% 1.71/0.58    inference(avatar_split_clause,[],[f46,f143])).
% 1.71/0.58  fof(f46,plain,(
% 1.71/0.58    v1_funct_1(sK2)),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f44,plain,(
% 1.71/0.58    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f43,f42])).
% 1.71/0.58  fof(f42,plain,(
% 1.71/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f43,plain,(
% 1.71/0.58    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f20,plain,(
% 1.71/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.71/0.58    inference(flattening,[],[f19])).
% 1.71/0.58  fof(f19,plain,(
% 1.71/0.58    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.71/0.58    inference(ennf_transformation,[],[f17])).
% 1.71/0.58  fof(f17,negated_conjecture,(
% 1.71/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.71/0.58    inference(negated_conjecture,[],[f16])).
% 1.71/0.58  fof(f16,conjecture,(
% 1.71/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.71/0.58  fof(f141,plain,(
% 1.71/0.58    spl4_11),
% 1.71/0.58    inference(avatar_split_clause,[],[f47,f138])).
% 1.71/0.58  fof(f47,plain,(
% 1.71/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f136,plain,(
% 1.71/0.58    spl4_10),
% 1.71/0.58    inference(avatar_split_clause,[],[f48,f133])).
% 1.71/0.58  fof(f48,plain,(
% 1.71/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f131,plain,(
% 1.71/0.58    spl4_9),
% 1.71/0.58    inference(avatar_split_clause,[],[f49,f128])).
% 1.71/0.58  fof(f49,plain,(
% 1.71/0.58    v1_funct_1(sK3)),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f126,plain,(
% 1.71/0.58    spl4_8),
% 1.71/0.58    inference(avatar_split_clause,[],[f50,f123])).
% 1.71/0.58  fof(f50,plain,(
% 1.71/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f121,plain,(
% 1.71/0.58    spl4_7),
% 1.71/0.58    inference(avatar_split_clause,[],[f51,f118])).
% 1.71/0.58  fof(f51,plain,(
% 1.71/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f116,plain,(
% 1.71/0.58    spl4_6),
% 1.71/0.58    inference(avatar_split_clause,[],[f52,f113])).
% 1.71/0.58  fof(f52,plain,(
% 1.71/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f111,plain,(
% 1.71/0.58    spl4_5),
% 1.71/0.58    inference(avatar_split_clause,[],[f53,f108])).
% 1.71/0.58  fof(f53,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f106,plain,(
% 1.71/0.58    spl4_4),
% 1.71/0.58    inference(avatar_split_clause,[],[f54,f103])).
% 1.71/0.58  fof(f54,plain,(
% 1.71/0.58    v2_funct_1(sK2)),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f101,plain,(
% 1.71/0.58    ~spl4_3),
% 1.71/0.58    inference(avatar_split_clause,[],[f55,f98])).
% 1.71/0.58  fof(f55,plain,(
% 1.71/0.58    k1_xboole_0 != sK0),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f96,plain,(
% 1.71/0.58    ~spl4_2),
% 1.71/0.58    inference(avatar_split_clause,[],[f56,f93])).
% 1.71/0.58  fof(f56,plain,(
% 1.71/0.58    k1_xboole_0 != sK1),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  fof(f91,plain,(
% 1.71/0.58    ~spl4_1),
% 1.71/0.58    inference(avatar_split_clause,[],[f57,f88])).
% 1.71/0.58  fof(f57,plain,(
% 1.71/0.58    k2_funct_1(sK2) != sK3),
% 1.71/0.58    inference(cnf_transformation,[],[f44])).
% 1.71/0.58  % SZS output end Proof for theBenchmark
% 1.71/0.58  % (22599)------------------------------
% 1.71/0.58  % (22599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (22599)Termination reason: Refutation
% 1.71/0.58  
% 1.71/0.58  % (22599)Memory used [KB]: 6652
% 1.71/0.58  % (22599)Time elapsed: 0.132 s
% 1.71/0.58  % (22599)------------------------------
% 1.71/0.58  % (22599)------------------------------
% 1.71/0.58  % (22577)Success in time 0.225 s
%------------------------------------------------------------------------------
