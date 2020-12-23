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
% DateTime   : Thu Dec  3 13:08:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 339 expanded)
%              Number of leaves         :   33 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  659 (1308 expanded)
%              Number of equality atoms :   57 ( 105 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f84,f88,f92,f96,f132,f136,f140,f148,f152,f156,f160,f186,f218,f222,f228,f243,f251])).

fof(f251,plain,
    ( ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | spl6_12
    | ~ spl6_15
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | spl6_12
    | ~ spl6_15
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f249,f230])).

fof(f230,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_29 ),
    inference(resolution,[],[f227,f168])).

fof(f168,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f167,f110])).

fof(f110,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f104,f109])).

fof(f109,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f91,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f104,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f80,f97])).

fof(f97,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f91,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f80,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f76,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f167,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK4))
        | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f166,f56])).

fof(f56,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f166,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK4)
        | ~ r2_hidden(X1,k1_relat_1(sK4))
        | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f162,f131])).

fof(f131,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f162,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK4)
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X1,k1_relat_1(sK4))
        | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl6_15 ),
    inference(resolution,[],[f147,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f147,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_15
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f227,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl6_29
  <=> r2_hidden(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f249,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_12
    | ~ spl6_27
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f248,f217])).

fof(f217,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl6_27
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f248,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_12
    | ~ spl6_31 ),
    inference(superposition,[],[f135,f242])).

fof(f242,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_31
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f135,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_12
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f243,plain,
    ( spl6_31
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f233,f216,f94,f90,f86,f75,f71,f67,f63,f59,f55,f241])).

fof(f59,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f63,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f67,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f86,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f94,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f233,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f232,f217])).

fof(f232,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f213,f72])).

fof(f72,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f212,f76])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_partfun1(sK4,sK0)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f211,f56])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_partfun1(sK4,sK0)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f124,f91])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f123,f68])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f122,f87])).

fof(f87,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f121,f60])).

fof(f60,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f64,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK1)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,sK1)
        | ~ v1_partfun1(X0,sK0)
        | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X1)
      | ~ v1_partfun1(X4,X0)
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

fof(f95,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f228,plain,
    ( spl6_29
    | spl6_4
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f224,f220,f67,f226])).

fof(f220,plain,
    ( spl6_28
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f224,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | spl6_4
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f223,f68])).

fof(f223,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f221,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f221,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl6_28
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f214,f184,f154,f138,f82,f59,f220])).

fof(f82,plain,
    ( spl6_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f138,plain,
    ( spl6_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f154,plain,
    ( spl6_17
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f184,plain,
    ( spl6_20
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f214,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(resolution,[],[f203,f83])).

fof(f83,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(superposition,[],[f172,f185])).

fof(f185,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f171,f60])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f169,f139])).

fof(f139,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_17 ),
    inference(resolution,[],[f155,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f155,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f218,plain,
    ( spl6_27
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f202,f94,f86,f71,f63,f59,f216])).

fof(f202,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f127,f72])).

fof(f127,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f126,f64])).

fof(f126,plain,
    ( ! [X3] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X3,sK1)
        | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f125,f87])).

fof(f125,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X3,sK1)
        | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f115,f60])).

fof(f115,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X3,sK1)
        | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3) )
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f186,plain,
    ( spl6_20
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f177,f158,f150,f138,f184])).

fof(f150,plain,
    ( spl6_16
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f158,plain,
    ( spl6_18
  <=> v1_partfun1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f177,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f176,f139])).

fof(f176,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f175,f151])).

fof(f151,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f175,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_18 ),
    inference(resolution,[],[f159,f45])).

fof(f159,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl6_18
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f120,f94,f86,f67,f59,f158])).

fof(f120,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f119,f87])).

fof(f119,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f118,f60])).

fof(f118,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f113,f68])).

fof(f113,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f156,plain,
    ( spl6_17
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f112,f94,f154])).

fof(f112,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f152,plain,
    ( spl6_16
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f111,f94,f150])).

fof(f111,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f51])).

fof(f148,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f98,f90,f146])).

fof(f98,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f91,f52])).

fof(f140,plain,
    ( spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f128,f94,f138])).

fof(f128,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f116,f48])).

fof(f116,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f47])).

fof(f136,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f33,f134])).

fof(f33,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f132,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f109,f90,f130])).

fof(f96,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,
    ( spl6_7
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f79,f71,f63,f82])).

fof(f79,plain,
    ( r2_hidden(sK5,sK1)
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f78,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f50])).

fof(f77,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f40,f67])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f59])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:28:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (13229)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.41  % (13238)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.42  % (13229)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f252,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f84,f88,f92,f96,f132,f136,f140,f148,f152,f156,f160,f186,f218,f222,f228,f243,f251])).
% 0.20/0.43  fof(f251,plain,(
% 0.20/0.43    ~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | spl6_12 | ~spl6_15 | ~spl6_27 | ~spl6_29 | ~spl6_31),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f250])).
% 0.20/0.43  fof(f250,plain,(
% 0.20/0.43    $false | (~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | spl6_12 | ~spl6_15 | ~spl6_27 | ~spl6_29 | ~spl6_31)),
% 0.20/0.43    inference(subsumption_resolution,[],[f249,f230])).
% 0.20/0.43  fof(f230,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_15 | ~spl6_29)),
% 0.20/0.43    inference(resolution,[],[f227,f168])).
% 0.20/0.43  fof(f168,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,sK0) | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | (~spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_15)),
% 0.20/0.43    inference(forward_demodulation,[],[f167,f110])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK4) | (~spl6_6 | ~spl6_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f104,f109])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    v1_relat_1(sK4) | ~spl6_9),
% 0.20/0.43    inference(subsumption_resolution,[],[f102,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK4) | ~spl6_9),
% 0.20/0.43    inference(resolution,[],[f91,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f90])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    spl6_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl6_6 | ~spl6_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f80,f97])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    v4_relat_1(sK4,sK0) | ~spl6_9),
% 0.20/0.43    inference(resolution,[],[f91,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ~v4_relat_1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_6),
% 0.20/0.43    inference(resolution,[],[f76,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f75])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.43  fof(f167,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK4)) | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | (~spl6_1 | ~spl6_11 | ~spl6_15)),
% 0.20/0.43    inference(subsumption_resolution,[],[f166,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    v1_funct_1(sK4) | ~spl6_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl6_1 <=> v1_funct_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    ( ! [X1] : (~v1_funct_1(sK4) | ~r2_hidden(X1,k1_relat_1(sK4)) | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | (~spl6_11 | ~spl6_15)),
% 0.20/0.43    inference(subsumption_resolution,[],[f162,f131])).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    v1_relat_1(sK4) | ~spl6_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f130])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    spl6_11 <=> v1_relat_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.43  fof(f162,plain,(
% 0.20/0.43    ( ! [X1] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X1,k1_relat_1(sK4)) | k7_partfun1(sK2,sK4,X1) = k1_funct_1(sK4,X1)) ) | ~spl6_15),
% 0.20/0.43    inference(resolution,[],[f147,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    v5_relat_1(sK4,sK2) | ~spl6_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f146])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    spl6_15 <=> v5_relat_1(sK4,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.43  fof(f227,plain,(
% 0.20/0.43    r2_hidden(k1_funct_1(sK3,sK5),sK0) | ~spl6_29),
% 0.20/0.43    inference(avatar_component_clause,[],[f226])).
% 0.20/0.43  fof(f226,plain,(
% 0.20/0.43    spl6_29 <=> r2_hidden(k1_funct_1(sK3,sK5),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.43  fof(f249,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_12 | ~spl6_27 | ~spl6_31)),
% 0.20/0.43    inference(forward_demodulation,[],[f248,f217])).
% 0.20/0.43  fof(f217,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~spl6_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f216])).
% 0.20/0.43  fof(f216,plain,(
% 0.20/0.43    spl6_27 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.43  fof(f248,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_12 | ~spl6_31)),
% 0.20/0.43    inference(superposition,[],[f135,f242])).
% 0.20/0.43  fof(f242,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_31),
% 0.20/0.43    inference(avatar_component_clause,[],[f241])).
% 0.20/0.43  fof(f241,plain,(
% 0.20/0.43    spl6_31 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f134])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    spl6_12 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.43  fof(f243,plain,(
% 0.20/0.43    spl6_31 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_27),
% 0.20/0.43    inference(avatar_split_clause,[],[f233,f216,f94,f90,f86,f75,f71,f67,f63,f59,f55,f241])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl6_2 <=> v1_funct_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl6_3 <=> v1_xboole_0(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl6_4 <=> v1_xboole_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    spl6_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl6_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.43  fof(f233,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_27)),
% 0.20/0.43    inference(forward_demodulation,[],[f232,f217])).
% 0.20/0.43  fof(f232,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.43    inference(resolution,[],[f213,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f213,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f212,f76])).
% 0.20/0.43  fof(f212,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f211,f56])).
% 0.20/0.43  fof(f211,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(X0,sK1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.43    inference(resolution,[],[f124,f91])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_8 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f123,f68])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0) | spl6_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v1_xboole_0(sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_2 | spl6_3 | ~spl6_8 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f122,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    v1_funct_2(sK3,sK1,sK0) | ~spl6_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f86])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (~spl6_2 | spl6_3 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f121,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    v1_funct_1(sK3) | ~spl6_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f59])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | (spl6_3 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f114,f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ~v1_xboole_0(sK1) | spl6_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f63])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X2,sK1) | ~v1_partfun1(X0,sK0) | k3_funct_2(sK1,X1,k8_funct_2(sK1,sK0,X1,sK3,X0),X2) = k1_funct_1(X0,k3_funct_2(sK1,sK0,sK3,X2))) ) | ~spl6_10),
% 0.20/0.43    inference(resolution,[],[f95,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | v1_xboole_0(X0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f94])).
% 0.20/0.43  fof(f228,plain,(
% 0.20/0.43    spl6_29 | spl6_4 | ~spl6_28),
% 0.20/0.43    inference(avatar_split_clause,[],[f224,f220,f67,f226])).
% 0.20/0.43  fof(f220,plain,(
% 0.20/0.43    spl6_28 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    r2_hidden(k1_funct_1(sK3,sK5),sK0) | (spl6_4 | ~spl6_28)),
% 0.20/0.43    inference(subsumption_resolution,[],[f223,f68])).
% 0.20/0.43  fof(f223,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | r2_hidden(k1_funct_1(sK3,sK5),sK0) | ~spl6_28),
% 0.20/0.43    inference(resolution,[],[f221,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.43  fof(f221,plain,(
% 0.20/0.43    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f220])).
% 0.20/0.43  fof(f222,plain,(
% 0.20/0.43    spl6_28 | ~spl6_2 | ~spl6_7 | ~spl6_13 | ~spl6_17 | ~spl6_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f214,f184,f154,f138,f82,f59,f220])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl6_7 <=> r2_hidden(sK5,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    spl6_13 <=> v1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    spl6_17 <=> v5_relat_1(sK3,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    spl6_20 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.43  fof(f214,plain,(
% 0.20/0.43    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | (~spl6_2 | ~spl6_7 | ~spl6_13 | ~spl6_17 | ~spl6_20)),
% 0.20/0.43    inference(resolution,[],[f203,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    r2_hidden(sK5,sK1) | ~spl6_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f82])).
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,sK1) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_13 | ~spl6_17 | ~spl6_20)),
% 0.20/0.43    inference(superposition,[],[f172,f185])).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    sK1 = k1_relat_1(sK3) | ~spl6_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f184])).
% 0.20/0.43  fof(f172,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_13 | ~spl6_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f171,f60])).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_13 | ~spl6_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f169,f139])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl6_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f138])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | ~spl6_17),
% 0.20/0.43    inference(resolution,[],[f155,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    v5_relat_1(sK3,sK0) | ~spl6_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f154])).
% 0.20/0.43  fof(f218,plain,(
% 0.20/0.43    spl6_27 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f202,f94,f86,f71,f63,f59,f216])).
% 0.20/0.43  fof(f202,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 0.20/0.43    inference(resolution,[],[f127,f72])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    ( ! [X3] : (~m1_subset_1(X3,sK1) | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3)) ) | (~spl6_2 | spl6_3 | ~spl6_8 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f126,f64])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    ( ! [X3] : (v1_xboole_0(sK1) | ~m1_subset_1(X3,sK1) | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3)) ) | (~spl6_2 | ~spl6_8 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f125,f87])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    ( ! [X3] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X3,sK1) | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3)) ) | (~spl6_2 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f115,f60])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    ( ! [X3] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X3,sK1) | k3_funct_2(sK1,sK0,sK3,X3) = k1_funct_1(sK3,X3)) ) | ~spl6_10),
% 0.20/0.43    inference(resolution,[],[f95,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    spl6_20 | ~spl6_13 | ~spl6_16 | ~spl6_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f177,f158,f150,f138,f184])).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    spl6_16 <=> v4_relat_1(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    spl6_18 <=> v1_partfun1(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    sK1 = k1_relat_1(sK3) | (~spl6_13 | ~spl6_16 | ~spl6_18)),
% 0.20/0.43    inference(subsumption_resolution,[],[f176,f139])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl6_16 | ~spl6_18)),
% 0.20/0.43    inference(subsumption_resolution,[],[f175,f151])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    v4_relat_1(sK3,sK1) | ~spl6_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f150])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    ~v4_relat_1(sK3,sK1) | sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl6_18),
% 0.20/0.43    inference(resolution,[],[f159,f45])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    v1_partfun1(sK3,sK1) | ~spl6_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f158])).
% 0.20/0.43  fof(f160,plain,(
% 0.20/0.43    spl6_18 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f120,f94,f86,f67,f59,f158])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    v1_partfun1(sK3,sK1) | (~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f119,f87])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1) | (~spl6_2 | spl6_4 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f118,f60])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1) | (spl6_4 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f113,f68])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    v1_xboole_0(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_partfun1(sK3,sK1) | ~spl6_10),
% 0.20/0.43    inference(resolution,[],[f95,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.43    inference(flattening,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    spl6_17 | ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f112,f94,f154])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    v5_relat_1(sK3,sK0) | ~spl6_10),
% 0.20/0.43    inference(resolution,[],[f95,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    spl6_16 | ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f111,f94,f150])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    v4_relat_1(sK3,sK1) | ~spl6_10),
% 0.20/0.43    inference(resolution,[],[f95,f51])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    spl6_15 | ~spl6_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f98,f90,f146])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    v5_relat_1(sK4,sK2) | ~spl6_9),
% 0.20/0.43    inference(resolution,[],[f91,f52])).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    spl6_13 | ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f128,f94,f138])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl6_10),
% 0.20/0.43    inference(subsumption_resolution,[],[f116,f48])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) | ~spl6_10),
% 0.20/0.43    inference(resolution,[],[f95,f47])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ~spl6_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f134])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f11])).
% 0.20/0.43  fof(f11,conjecture,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    spl6_11 | ~spl6_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f109,f90,f130])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f38,f94])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl6_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f35,f90])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    spl6_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f37,f86])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl6_7 | spl6_3 | ~spl6_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f71,f63,f82])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    r2_hidden(sK5,sK1) | (spl6_3 | ~spl6_5)),
% 0.20/0.43    inference(subsumption_resolution,[],[f78,f64])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl6_5),
% 0.20/0.43    inference(resolution,[],[f72,f50])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl6_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f75])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    v1_partfun1(sK4,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl6_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f71])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    m1_subset_1(sK5,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ~spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f40,f67])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ~spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f39,f63])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ~v1_xboole_0(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl6_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f36,f59])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    v1_funct_1(sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl6_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f55])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    v1_funct_1(sK4)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (13229)------------------------------
% 0.20/0.43  % (13229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (13229)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (13229)Memory used [KB]: 6396
% 0.20/0.43  % (13229)Time elapsed: 0.039 s
% 0.20/0.43  % (13229)------------------------------
% 0.20/0.43  % (13229)------------------------------
% 0.20/0.44  % (13224)Success in time 0.085 s
%------------------------------------------------------------------------------
